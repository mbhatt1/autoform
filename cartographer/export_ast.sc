// Joern query: export each method's AST as a language-neutral JSON tree.
//
// This is Layer 3 (Transpiler), and it is deterministic — no LLM anywhere on this path.
//
// The reason one exporter suffices for many languages is that Joern has already done the
// normalization: C, C++, Java, JavaScript, Python, Kotlin and binaries all land in the
// same CPG node vocabulary (CALL / IDENTIFIER / LITERAL / CONTROL_STRUCTURE / RETURN /
// BLOCK / FIELD_IDENTIFIER / METHOD_REF / TYPE_REF), with operators as `<operator>.*`
// calls. We map that vocabulary onto `Autoform.Core`, and anything we do not recognise
// becomes a *hole tagged with the node label that produced it*. Nothing is silently
// dropped, and nothing is guessed: where a construct cannot be translated faithfully the
// hole label says precisely which shape defeated us.
//
// Beyond the per-node mapping, the exporter answers three whole-program questions that
// the node vocabulary alone cannot: which names are module-level (exported as one
// `setGlobal` initializer per file), which function values capture an enclosing scope
// (`closure` rather than `fnref`), and — because the CPG is multi-language — which
// operators change meaning under the source dialect (a C `char*` is an address, so `+`
// and `<` are not the string operations they look like).
//
// Run: joern --script cartographer/export_ast.sc --param cpgPath=... --param out=ast.json

import io.shiftleft.codepropertygraph.generated.nodes._

@main def exec(cpgPath: String, out: String = "ast.json", maxMethods: Int = 100000) = {
  importCpg(cpgPath)

  // CPG operator name -> Core binary operator.
  //
  // `floorDiv` is Python's `//`. It maps to "/" because the Core semantics is
  // dialect-parameterized: `Dialect.python` already floors, `Dialect.cLike` truncates.
  //
  // Deliberately absent: `<operator>.and` / `<operator>.or` / `xor` / shifts. Those are
  // *bitwise*, not logical (`logicalAnd` / `logicalOr` are the logical ones), and Core has
  // no bitwise ops. Mapping them to "&&"/"||" — as this exporter previously did — is a
  // silently wrong answer, which is worse than a hole.
  val binops = Map(
    "<operator>.addition" -> "+", "<operator>.subtraction" -> "-",
    "<operator>.multiplication" -> "*", "<operator>.division" -> "/",
    "<operator>.floorDiv" -> "/",
    "<operator>.modulo" -> "%", "<operator>.lessThan" -> "<",
    "<operator>.lessEqualsThan" -> "<=", "<operator>.greaterThan" -> ">",
    "<operator>.greaterEqualsThan" -> ">=", "<operator>.equals" -> "==",
    "<operator>.notEquals" -> "!=", "<operator>.logicalAnd" -> "&&",
    "<operator>.logicalOr" -> "||"
  )
  // Operators whose Core meaning is wrong when an operand is a C `char*`. `+`/`-` are
  // pointer arithmetic, not concatenation; the orderings and equalities compare
  // addresses, not contents. Each keeps its own hole label so the cause is separable in
  // the ledger.
  val cStringUnsafe = Map(
    "<operator>.addition"           -> "cstr:pointer-arith",
    "<operator>.subtraction"        -> "cstr:pointer-arith",
    "<operator>.assignmentPlus"     -> "cstr:pointer-arith",
    "<operator>.assignmentMinus"    -> "cstr:pointer-arith",
    "<operator>.lessThan"           -> "cstr:address-compare",
    "<operator>.lessEqualsThan"     -> "cstr:address-compare",
    "<operator>.greaterThan"        -> "cstr:address-compare",
    "<operator>.greaterEqualsThan"  -> "cstr:address-compare",
    "<operator>.equals"             -> "cstr:address-equality",
    "<operator>.notEquals"          -> "cstr:address-equality"
  )

  val unops = Map(
    "<operator>.minus" -> "-", "<operator>.logicalNot" -> "!", "<operator>.not" -> "!"
  )

  def hole(label: String): ujson.Obj  = ujson.Obj("k" -> "hole", "label" -> label)
  def holeS(label: String): ujson.Obj = ujson.Obj("k" -> "holeS", "label" -> label)
  val skip = ujson.Obj("k" -> "skip")

  def kidsOf(n: AstNode): List[AstNode] = n.astChildren.collect { case a: AstNode => a }.l

  /** Joern's ARGUMENT index: -1 = the callee/receiver expression, 0 = the implicit
    * `self`/`this` the Python frontend threads through, >=1 = the real arguments. */
  def aidx(n: AstNode): Int = n match {
    case e: Expression => e.argumentIndex
    case _             => -1
  }

  def isOp(n: AstNode, op: String): Boolean = n match {
    case c: Call => c.methodFullName == op
    case _       => false
  }

  // ---- Python private name mangling -----------------------------------------
  //
  // Inside a class body, CPython rewrites any identifier with **two or more leading
  // underscores and at most one trailing underscore** to `_<Class><name>`, with leading
  // underscores stripped from the class name. So `self.__maxsize` in `class Cache` is
  // really the attribute `_Cache__maxsize`, and `class _Foo`'s `__bar` is `_Foo__bar`.
  //
  // The CPG carries the *unmangled* source text on every FIELD_IDENTIFIER, so translating
  // it literally produces a read that misses and yields `unit` — the silently-wrong
  // category, not the absent category. This is the same shape as the `floorDiv` and
  // `<operator>.and` finds.
  //
  // The rewrite is **lexical and compile-time**: it depends on where the code is written,
  // not on the receiver's runtime class. That is exactly why it matters here — `Cache`'s
  // methods reach `_Cache__data` even when `self` is an `LRUCache`.
  //
  // A class's lexical path is its TypeDecl `fullName`, so the enclosing class is found the
  // same way closures found their enclosing function: walk the `fullName` prefixes and
  // test *membership* in a map of known full names, taking the simple name from the node
  // rather than splitting the string (see `enclosingFunctionBindings` for why).
  val classByFullName: Map[String, String] =
    cpg.typeDecl.isExternal(false).l
      .filter(_.method.name.l.contains("<body>"))
      .map(t => t.fullName -> t.name).toMap

  val enclClassCache = collection.mutable.HashMap.empty[String, Option[String]]

  /** The innermost class lexically enclosing `fn`, by simple name. */
  def enclosingClassOf(fn: String): Option[String] =
    enclClassCache.getOrElseUpdate(fn, {
      def go(cur: String): Option[String] = {
        val i = cur.lastIndexOf('.')
        if (i < 0) None
        else {
          val parent = cur.substring(0, i)
          classByFullName.get(parent).orElse(go(parent))
        }
      }
      go(fn)
    })

  /** CPython's rule, exactly: 2+ leading underscores, at most one trailing. `__x__` and
    * `_x` are untouched; a class whose name is all underscores does not mangle. */
  def mangleName(name: String, cls: Option[String]): String = cls match {
    case Some(c) if name.startsWith("__") && !name.endsWith("__") =>
      val bare = c.dropWhile(_ == '_')
      if (bare.isEmpty) name else "_" + bare + name
    case _ => name
  }

  /** The class lexically enclosing the method currently being translated. Mangling is a
    * property of the *writing* site, so this is the method's own class, never the
    * receiver's. */
  var currentClass: Option[String] = None

  /** `e.f` — a fieldAccess is [receiver, FIELD_IDENTIFIER], except that when the Python
    * frontend has *resolved* the attribute it prepends the resolved METHOD_REF/TYPE_REF,
    * giving [METHOD_REF, receiver, FIELD_IDENTIFIER]. */
  def asField(n: AstNode): Option[(AstNode, String)] = n match {
    case c: Call if c.methodFullName == "<operator>.fieldAccess" =>
      val k = kidsOf(c)
      k.lastOption match {
        // The attribute name is mangled here, once, so every consumer — `field`,
        // `setField`, and the `mcall` method name, which all read it from this one
        // place — stays consistent with the definition names mangled below.
        case Some(f: FieldIdentifier) if k.size >= 2 =>
          Some((k(k.size - 2), mangleName(f.canonicalName, currentClass)))
        case _                                       => None
      }
    case _ => None
  }

  /** A resolved attribute reference: `Cls.meth` where Joern already knows the target. */
  def resolvedRef(n: AstNode): Option[AstNode] = n match {
    case c: Call if c.methodFullName == "<operator>.fieldAccess" =>
      kidsOf(c) match {
        case (m: MethodRef) :: _ :: _ :: Nil => Some(m)
        case (t: TypeRef) :: _ :: _ :: Nil   => Some(t)
        case _                               => None
      }
    case _ => None
  }

  /** `e[i]`. */
  def asIndex(n: AstNode): Option[(AstNode, AstNode)] = n match {
    case c: Call if c.methodFullName == "<operator>.indexAccess" =>
      kidsOf(c) match {
        case a :: b :: Nil => Some((a, b))
        case _             => None
      }
    case _ => None
  }

  /** Re-evaluable without observable effect. Augmented assignment (`o.f += 1`) is
    * desugared by duplicating the target expression, which is only faithful if
    * evaluating it twice is the same as evaluating it once. */
  def pureNode(n: AstNode): Boolean = n match {
    case _: Identifier | _: Literal | _: MethodParameterIn | _: TypeRef | _: MethodRef => true
    case c: Call if c.methodFullName == "<operator>.fieldAccess" =>
      asField(c).exists(p => pureNode(p._1))
    case c: Call if c.methodFullName == "<operator>.indexAccess" =>
      asIndex(c).exists(p => pureNode(p._1) && pureNode(p._2))
    case _ => false
  }

  /** `pureNode`, plus the container displays. Core's lists/tuples/dicts are *values*
    * (`Val.list`/`Val.tuple`/`Val.dict`), not heap objects, so building one allocates
    * nothing observable and re-evaluating `{}` is indistinguishable from evaluating it
    * once. This is what makes the frontend's `tmp0 = {}; tmp0` blocks removable. */
  def pureExpr(n: AstNode): Boolean = pureNode(n) || (n match {
    case c: Call if c.methodFullName == "<operator>.listLiteral" ||
                    c.methodFullName == "<operator>.tupleLiteral" ||
                    c.methodFullName == "<operator>.dictLiteral" => kidsOf(c).forall(pureExpr)
    case _ => false
  })

  // Classes declared in the analysed code. A call to one of these is construction, not
  // a plain function call. Joern usually marks it by resolving to `...Cls.__init__`, but
  // not always (unresolved bases, decorated classes), so we keep the name set as a
  // second, still-conservative signal.
  // A TYPE_DECL is also emitted for every *function* (its function-object type), so the
  // name alone would classify `f(x)` as construction. A TYPE_DECL from a real `class`
  // statement is the one carrying a `<body>` method for the class body.
  val classNames: Set[String] =
    cpg.typeDecl.isExternal(false).l
      .filter(_.method.name.l.contains("<body>"))
      .map(_.name).filterNot(_.contains("<")).toSet

  // ---- classes with a builtin base type --------------------------------------
  //
  // `class _HashedTuple(tuple)` is not an ordinary class: in CPython the instance *is* a
  // tuple, and `hashkey(0) == (0,)` is `True`. Core models this with `Val.bobj`, keyed by
  // `Program.builtinBases`, and the base is visible right here in the CPG and was
  // previously discarded. See STRATEGY.md §31/§33/§34 and `Autoform/BuiltinBase.lean`.
  //
  // Deliberately conservative in three ways, because a *wrong* base is a silent wrong
  // answer while a missing one is just the old opaque-reference behaviour:
  //
  //   * exactly one base, so multiple inheritance is never guessed at;
  //   * that base must be one of the four builtins `Core.BuiltinBase` models — `object`,
  //     `Exception` and everything transitive are left alone;
  //   * a short class name that resolves to two *different* bases anywhere in the corpus
  //     is dropped entirely, because `Expr.alloc` carries only the short name.
  val modelledBases = Set("tuple", "list", "dict", "str")

  val builtinBaseRows: List[(String, String, String)] =
    cpg.typeDecl.isExternal(false).l
      .filter(_.method.name.l.contains("<body>"))
      .filterNot(_.name.contains("<"))
      .flatMap { td =>
        val bases = td.inheritsFromTypeFullName
          .filterNot(b => b.isEmpty || b == "ANY" || b == "object" || b.endsWith(".object"))
        if (bases.size != 1) None
        else {
          // `tuple`, `builtins.tuple`, `__builtin.tuple`, `<unresolvedNamespace>.tuple`:
          // the frontends disagree on the prefix, never on the last segment.
          val short = bases.head.split('.').last.split(':').last
          if (modelledBases.contains(short)) Some((td.filename, td.name, short)) else None
        }
      }

  val conflictingBaseNames: Set[String] =
    builtinBaseRows.groupBy(_._2)
      .collect { case (n, rs) if rs.map(_._3).distinct.size > 1 => n }.toSet

  /** Builtin bases of the classes declared in one file, by short class name. */
  val classBasesByFile: Map[String, Map[String, String]] =
    builtinBaseRows.filterNot(r => conflictingBaseNames.contains(r._2))
      .groupBy(_._1).map { case (f, rs) => f -> rs.map(r => r._2 -> r._3).toMap }

  // ---- lexical scope analysis ------------------------------------------------
  //
  // Joern's `fullName` *is* the lexical nesting path: `f.py:<module>.outer.inner`,
  // `f.py:<module>.Cls.<body>.meth`. So the scope chain is recoverable by prefix, with no
  // need to walk AST parent edges (which differ between frontends).
  //
  // We need it for exactly one decision: is a `METHOD_REF` a plain `fnref` (a top-level
  // function, resolvable by name) or a `closure` (it reads a variable of an enclosing
  // *function*)? Module-level names are not captures — `Expr.name` falls back to the
  // globals frame — and class bodies are not a closure scope in Python, so only enclosing
  // function scopes count.
  val allMethods   = cpg.method.isExternal(false).l
  val methodByName = allMethods.map(m => m.fullName -> m).toMap

  /** Names a method binds itself: parameters plus identifier assignment targets — which
    * is exactly Python's rule (a name assigned anywhere in a body is local throughout),
    * minus the names a `global`/`nonlocal` statement explicitly un-localises.
    *
    * `m.local` is deliberately **not** used. A CPG fact that defeats the obvious version
    * of this analysis: pysrc2cpg emits a LOCAL in the *inner* method for every name it
    * closes over, and for module-level names it reads — `inner` has `locals = [k]` even
    * though `k` is the enclosing function's parameter. LOCAL here is a *reference*
    * declaration, not a binding, so trusting it reports that nothing ever captures. */
  val boundOf: Map[String, Set[String]] = allMethods.map { m =>
    val assigned = m.body.ast.isCall
      .filter(c => c.methodFullName.startsWith("<operator>.assignment"))
      .l.flatMap(c => kidsOf(c).headOption).collect { case i: Identifier => i.name }.toSet
    val unlocalised = m.body.ast.collect {
      case u: Unknown if u.code.trim.startsWith("global ") || u.code.trim.startsWith("nonlocal ") =>
        u.code.trim.dropWhile(_ != ' ').split(",").map(_.trim).filter(_.nonEmpty)
    }.l.flatten.toSet
    m.fullName -> ((m.parameter.name.toSet ++ assigned) -- unlocalised)
  }.toMap

  /** Identifier names a method mentions in its own body (not its nested methods'). */
  val usedOf: Map[String, Set[String]] = allMethods.map { m =>
    m.fullName -> m.body.ast.isIdentifier.filter(_.method.fullName == m.fullName).name.toSet
  }.toMap

  /** Methods lexically nested one level inside `fn`. */
  val nestedOf: Map[String, List[String]] =
    allMethods.map(_.fullName).groupBy { fn =>
      val i = fn.lastIndexOf('.')
      if (i < 0) "" else fn.substring(0, i)
    }.withDefaultValue(Nil)

  /** Free names of a method, including those its nested definitions leave free:
    *   free(m) = (used(m) ∪ ⋃ free(nested)) \ bound(m)
    * The nesting relation is a prefix order, so this terminates. */
  def freeOf(fn: String): Set[String] = {
    val used   = usedOf.getOrElse(fn, Set.empty)
    val inner  = nestedOf(fn).filter(_ != fn).flatMap(freeOf).toSet
    (used ++ inner) -- boundOf.getOrElse(fn, Set.empty)
  }

  /** Names bound by the enclosing *function* scopes of `fn` — skipping `<module>`
    * (globals) and `<body>`/`<meta>` (class bodies, which Python does not close over). */
  def enclosingFunctionBindings(fn: String): Set[String] = {
    def go(cur: String, acc: Set[String]): Set[String] = {
      val i = cur.lastIndexOf('.')
      if (i < 0) acc
      else {
        val parent = cur.substring(0, i)
        // The *simple* name has to come from the node, not from splitting the fullName:
        // `cachetools/keys.py:<module>` ends in a dot-segment `py:<module>`, so string
        // surgery would classify the module scope as an ordinary function and report that
        // every module-level `def` captures the module.
        val isFunctionScope =
          methodByName.get(parent).exists(p => !p.name.startsWith("<"))
        go(parent, if (isFunctionScope) acc ++ boundOf.getOrElse(parent, Set.empty) else acc)
      }
    }
    go(fn, Set.empty)
  }

  /** Every file-level pseudo-method, keyed by its `fullName` (`pkg/mod.py:<module>`).
    * This is the import resolver's whole notion of "a module in the analysed program". */
  val moduleFullNames: Set[String] =
    allMethods.filter(m => m.name == "<module>" || m.name == "<global>").map(_.fullName).toSet

  /** The file-level pseudo-method for a slash-separated module path, if the analysed
    * program contains it — either `p.py` or the package `p/__init__.py`. */
  def moduleAt(path: String): Option[String] = {
    val a = path + ".py:<module>"
    val b = path + "/__init__.py:<module>"
    if (moduleFullNames.contains(a)) Some(a)
    else if (moduleFullNames.contains(b)) Some(b)
    else None
  }

  /** A function value that reads a variable of an enclosing function is a *closure*;
    * one that does not is an `fnref`, which is cheaper and needs no captured frame. */
  val capturesEnv: Map[String, Boolean] = allMethods.map { m =>
    m.fullName -> freeOf(m.fullName).intersect(enclosingFunctionBindings(m.fullName)).nonEmpty
  }.toMap

  /** A method *definition* mangles too: `def __touch` in `class LRUCache` is stored as
    * `_LRUCache__touch`. Reference and definition must be mangled together — mangling
    * only the reference would trade a silently-wrong field read for a silently
    * unresolvable call, which is not an improvement. */
  def mangledFullName(fn: String): String = methodByName.get(fn) match {
    case Some(m) if fn.endsWith(m.name) =>
      val mg = mangleName(m.name, enclosingClassOf(fn))
      if (mg == m.name) fn else fn.dropRight(m.name.length) + mg
    case _ => fn
  }

  /** `target` is the *unmangled* CPG fullName: capture analysis is keyed on it, and the
    * emitted name is mangled on the way out so it matches the exported definition. */
  def fnValue(target: String): ujson.Obj = {
    val out = mangledFullName(target)
    if (capturesEnv.getOrElse(target, false)) ujson.Obj("k" -> "closure", "f" -> out)
    else ujson.Obj("k" -> "fnref", "v" -> out)
  }

  /** A class used as a value. Usually an `fnref` — but a class *defined inside a function*
    * whose methods read that function's variables carries an environment, and `Expr.closure`
    * names a function, not a class. `Expr.classClosure` is the constructor for that case:
    * it captures the environment at the point the `class` statement runs, `Expr.alloc`
    * stores it on the instance, and method dispatch on such an instance resolves free
    * names against it. Handing back a plain `fnref` here — the thing this refused to do
    * while there was no constructor — would have produced methods whose names were unbound. */
  def typeValue(target: String): ujson.Obj = {
    val cls = target.stripSuffix("<meta>")
    val captures = allMethods.exists(m =>
      m.fullName.startsWith(cls + ".") && capturesEnv.getOrElse(m.fullName, false))
    if (captures) ujson.Obj("k" -> "classClosure", "c" -> target)
    else ujson.Obj("k" -> "fnref", "v" -> target)
  }

  // ---- per-method translation state ------------------------------------------
  // `moduleScope` is set while translating a `<module>`/`<global>` pseudo-method: every
  // identifier assignment there defines a module-level binding, so it becomes `setGlobal`.
  // `declaredGlobals` holds the names a `global x` statement rebound in the current
  // function, whose assignments must also write the globals frame rather than a local.
  var moduleScope     = false
  var declaredGlobals = Set.empty[String]
  // Set while translating a method from a C-family file, where a `char*` is an address,
  // not a string value.
  var cLikeFile       = false
  // The source file of the method being translated. `import` is resolved relative to it.
  var currentFile     = ""
  // Serial number for the flag variable `try/except/else` needs; nested `try`s in one
  // function must not share it, or the inner one's flag would drive the outer's `else`.
  var elseFlagSeq     = 0
  /** `t -> (receiver, method)` for every `t = r.m` in the method being translated, where
    * `r` is a plain identifier. The Python frontend's `with` lowering binds the context
    * manager's `__enter__`/`__exit__` this way and then calls the *temporary*, which
    * leaves a call with no name at all. See `boundMethodCall`. */
  var boundMethods    = Map.empty[String, (String, String)]
  /** Receiver name -> attribute names read off it anywhere in the method being
    * translated. Corroborates the second form of `boundMethodCall`. */
  var attrsOf         = Map.empty[String, Set[String]]

  /** Static evidence that an operand is a C string/array-of-char. Joern's C frontend
    * types both `char *s` and `"abc"` as `char*`, including on literals. */
  def isCString(n: AstNode): Boolean = {
    def t(x: AstNode): String = x match {
      case c: Call              => c.typeFullName
      case i: Identifier        => i.typeFullName
      case l: Literal           => l.typeFullName
      case p: MethodParameterIn => p.typeFullName
      case _                    => ""
    }
    val ty = t(n).replace(" ", "")
    ty.matches("""(const|volatile|signed|unsigned)*char(\*|\[.*\]).*""")
  }

  /** `import p.q` / `from <prefix> import <name>`.
    *
    * The Python frontend emits this as a call named `import` with two synthetic literals
    * — the (possibly dot-prefixed, possibly empty) package prefix and the imported name —
    * wrapped in an assignment that binds the resulting value. Those literals are unquoted
    * source fragments, not values, so translating them as expressions produced
    * `lit:unquoted` holes that said nothing about what the statement actually was.
    *
    * What the *statement* means is a binding, and sometimes the bound value is one we
    * already have: `from ._cached import _wrapper` names a function of this program, and
    * `from . import LRUCache` names a class of it. Those become the same `fnref`/`closure`
    * a direct reference would, so the binding is real and cross-module names resolve.
    *
    * What we refuse to invent is a **module object**. `import functools` binds a module,
    * and Core has no module value — `Val.fn` is a function or a class, so pointing a name
    * at `fnref "functools"` would claim `functools.reduce` is an attribute of a function.
    * That is the `fnref`-for-a-capturing-class mistake again, so it stays a hole; only the
    * label improves, from "an unquoted literal" to "a module value we cannot represent".
    *
    * Resolution is lexical and purely syntactic: leading dots count package levels up from
    * the importing file's directory, and the remainder is a path. No sys.path search, no
    * guessing — if the target is not a method or class of the analysed program, we say so. */
  def importValue(prefix: String, name: String): ujson.Obj = {
    val dots = prefix.takeWhile(_ == '.').length
    val rest = prefix.drop(dots)
    // `import x` / `import x.y` binds the *module* `x`, never a member.
    if (dots == 0 && rest.isEmpty) hole("import:module-value")
    else {
      val dir  = currentFile.split('/').dropRight(1).dropRight(math.max(dots - 1, 0)).toList
      val base = if (dots == 0) Nil else dir
      val segs = base ++ rest.split('.').filter(_.nonEmpty).toList
      val path = segs.mkString("/")
      moduleAt(path) match {
        case None => hole("import:unresolved")
        case Some(mod) =>
          val target = mod + "." + name
          if (methodByName.contains(target))        fnValue(target)
          else if (classByFullName.contains(target)) typeValue(target + "<meta>")
          // `from . import keys` where `keys` is a sibling *module*, not a member.
          else if (moduleAt(path + "/" + name).isDefined) hole("import:module-value")
          else hole("import:unresolved")
      }
    }
  }

  // ---- expressions ----------------------------------------------------------
  def expr(n: AstNode): ujson.Obj = n match {
    case l: Literal =>
      val c = l.code.trim
      val unquoted =
        if (c.length >= 2 && (c.head == '"' || c.head == '\'')) c.drop(1).dropRight(1) else c
      c.toIntOption match {
        case Some(i) => ujson.Obj("k" -> "int", "v" -> i)
        case None =>
          if (c == "True" || c == "true")        ujson.Obj("k" -> "bool", "v" -> true)
          else if (c == "False" || c == "false") ujson.Obj("k" -> "bool", "v" -> false)
          else if (c == "None" || c == "null" || c == "nil") ujson.Obj("k" -> "unit")
          // A float is not a string. Core has no floats, so this is a hole, not a lie.
          else if (c.matches("""[-+]?\d+\.\d*([eE][-+]?\d+)?|[-+]?\.\d+([eE][-+]?\d+)?"""))
            hole("lit:float")
          else if (c.headOption.exists(ch => ch == '"' || ch == '\''))
            ujson.Obj("k" -> "str", "v" -> unquoted)
          else if (c.isEmpty) ujson.Obj("k" -> "unit")
          // Unquoted, non-numeric literal code: the frontend synthesises these for
          // constructs like `import a.b`. Calling it a string would be inventing a value.
          else hole("lit:unquoted")
      }
    case i: Identifier        => ujson.Obj("k" -> "name", "v" -> i.name)
    case p: MethodParameterIn => ujson.Obj("k" -> "name", "v" -> p.name)
    // A function/method or a class used as a value. Whether it needs to carry the
    // enclosing environment is decided by `capturesEnv`, above.
    case m: MethodRef         => fnValue(m.methodFullName)
    case t: TypeRef           => typeValue(t.typeFullName)
    case c: Call              => callExpr(c)
    case b: Block             => blockExpr(b)
    case other                => hole("expr:" + other.label)
  }

  def exprs(ns: List[AstNode]): ujson.Arr = ujson.Arr.from(ns.map(expr))

  /** Substitute `name` occurrences in an already-translated tree. Used only for the
    * frontend's own `tmpN` temporaries, whose definitions we proved re-evaluable. */
  def substNames(v: ujson.Value, m: Map[String, ujson.Value]): ujson.Value = v match {
    case o: ujson.Obj =>
      val nm = for { k <- o.value.get("k") if k.str == "name"
                     x <- o.value.get("v"); r <- m.get(x.str) } yield r
      nm.getOrElse(ujson.Obj.from(o.value.map { case (k, x) => k -> substNames(x, m) }.toSeq))
    case a: ujson.Arr => ujson.Arr.from(a.value.map(substNames(_, m)))
    case other        => other
  }

  /** A BLOCK in *expression* position.
    *
    * pysrc2cpg lowers several expressions into a statement sequence ending in its value —
    * `d.pop(k)` becomes `tmp0 = d; tmp0.pop(k)`, `{}` becomes `tmp0 = {}; tmp0`. In
    * statement position `valueOf` splits that into a prelude plus a value, but an argument
    * has nowhere to put statements, so these were `expr:BLOCK` holes.
    *
    * They can be recovered exactly when the prelude is *inlinable*: every preceding
    * statement binds one of the frontend's own `tmpN` names to a re-evaluable expression.
    * Then substituting the definitions into the value is a pure renaming — no statement is
    * dropped (a pure binding has no effect) and no evaluation is reordered (the substituted
    * expression is evaluated exactly where the temporary was read, and evaluating it
    * earlier or later is unobservable). Hoisting an *impure* prelude out to the enclosing
    * statement would reorder it past the arguments evaluated before it, so anything that
    * does not fit the inlinable shape — generator expressions, most notably — stays a hole
    * with a label naming what defeated it. */
  def blockExpr(b: Block): ujson.Obj = {
    val ks = kidsOf(b).filterNot(_.isInstanceOf[Local])
    if (ks.isEmpty) hole("expr:empty-block")
    else {
      var subst = Map.empty[String, ujson.Value]
      var bad   = ""
      ks.init.foreach {
        case c: Call if c.methodFullName == "<operator>.assignment" =>
          kidsOf(c) match {
            case (i: Identifier) :: rhs :: Nil
                if i.name.matches("tmp\\d+") && pureExpr(rhs) =>
              subst += (i.name -> substNames(expr(rhs), subst))
            case (_: Identifier) :: rhs :: Nil => if (bad.isEmpty) bad = "expr:BLOCK-impure"
            case _                             => if (bad.isEmpty) bad = "expr:BLOCK-prelude"
          }
        // `tmp0 = <operator>.genExp` plus the loop that fills it: a generator expression,
        // which is lazy and has no Core representation at all.
        case n if n.isInstanceOf[Block] || n.isInstanceOf[ControlStructure] =>
          if (bad.isEmpty) bad = "expr:BLOCK-prelude"
        case _ => if (bad.isEmpty) bad = "expr:BLOCK-prelude"
      }
      val isGenExp = ks.exists(k => k.isInstanceOf[Call] &&
        k.asInstanceOf[Call].code.contains("<operator>.genExp"))
      if (isGenExp) hole("expr:genExp")
      else if (bad.nonEmpty) hole(bad)
      else substNames(expr(ks.last), subst) match {
        case o: ujson.Obj => o
        case _            => hole("expr:BLOCK")
      }
    }
  }

  /** A call whose callee is a *bound method held in a variable*.
    *
    * `with cm as x:` is lowered by pysrc2cpg to
    *
    *     manager_tmp0 = <cm>;  enter_tmp0 = manager_tmp0.__enter__
    *     exit_tmp0 = manager_tmp0.__exit__;  value_tmp0 = enter_tmp0()
    *     try: ... finally: __exit__()
    *
    * so the invocation carries no name — the callee is the temporary — while still
    * repeating the receiver at argument index 0, which is where the frontend always puts
    * the implicit `self`. Both halves of the method's identity are therefore present, just
    * split across two statements: the receiver on the call, the attribute name on the
    * assignment that produced the temporary. Rejoining them recovers the `mcall` exactly,
    * which is what makes `with` translatable rather than an unnamed call into nothing.
    *
    * The binding must name the *same* receiver the call passes, so this cannot mistake
    * `g = a.m; g()` for a call on some other object. */
  def boundMethodCall(c: Call, callee: Option[AstNode],
                      args: List[AstNode]): Option[ujson.Obj] =
    for {
      cal <- callee
      t   <- Option(cal).collect { case i: Identifier => i.name }
      // The receiver is where the Python frontend always puts it: argument index 0.
      r   <- c.astChildren.collect { case a: AstNode => a }.l
               .collectFirst { case i: Identifier if aidx(i) == 0 => i.name }
      // Two spellings, both grounded in this method's own CPG rather than assumed. The
      // frontend names the callee after the temporary for `__enter__` and after the
      // attribute itself for `__exit__`, so accept either — but only when the receiver
      // that the *binding* used is the receiver this call passes, or the attribute is one
      // this method is seen to read off that receiver. Neither can turn `g = a.m; g()`
      // into a call on some unrelated object.
      m   <- boundMethods.get(t).collect { case (br, bm) if br == r => bm }
               .orElse(if (attrsOf.getOrElse(r, Set.empty).contains(t)) Some(t) else None)
    } yield ujson.Obj("k" -> "mcall", "recv" -> ujson.Obj("k" -> "name", "v" -> r),
                      "m" -> mangleName(m, currentClass), "args" -> exprs(args))

  def callExpr(c: Call): ujson.Obj = {
    val kids = kidsOf(c)
    val mfn  = c.methodFullName
    // A `char*` is an address, not a string value. Core has one `Val.str` for Python's
    // `str` and C's `char*`, and its `+` concatenates while `<`/`>`/`==` compare contents
    // — all three are the wrong answer in C, where they are pointer arithmetic and
    // address comparison. This is the §12 lesson again: the constructs that *look* alike
    // across languages are the dangerous ones. So under a C-family dialect, an operand
    // with static `char*` evidence turns the whole operator into a hole.
    if (cLikeFile && kids.size == 2 && kids.exists(isCString) &&
        cStringUnsafe.contains(mfn))
      hole(cStringUnsafe(mfn))
    else if (binops.contains(mfn) && kids.size == 2)
      ujson.Obj("k" -> "binop", "op" -> binops(mfn), "a" -> expr(kids(0)), "b" -> expr(kids(1)))
    else if (unops.contains(mfn) && kids.size == 1)
      ujson.Obj("k" -> "unop", "op" -> unops(mfn), "a" -> expr(kids(0)))
    else if (mfn == "<operator>.indexAccess" && kids.size == 2)
      ujson.Obj("k" -> "index", "a" -> expr(kids(0)), "b" -> expr(kids(1)))
    else if (mfn == "<operator>.fieldAccess")
      resolvedRef(c).map(expr) getOrElse (asField(c) match {
        case Some((r, f)) => ujson.Obj("k" -> "field", "a" -> expr(r), "f" -> f)
        case None         => hole("op:fieldAccess-shape")
      })
    else if ((mfn == "<operator>.is" || mfn == "<operator>.isNot") && kids.size == 2)
      ujson.Obj("k" -> "isOp", "neg" -> (mfn == "<operator>.isNot"),
                "a" -> expr(kids(0)), "b" -> expr(kids(1)))
    else if ((mfn == "<operator>.in" || mfn == "<operator>.notIn") && kids.size == 2)
      ujson.Obj("k" -> "inOp", "neg" -> (mfn == "<operator>.notIn"),
                "a" -> expr(kids(0)), "b" -> expr(kids(1)))
    else if (mfn == "<operator>.conditional" && kids.size == 3)
      ujson.Obj("k" -> "cond", "c" -> expr(kids(0)), "t" -> expr(kids(1)), "e" -> expr(kids(2)))
    else if (mfn == "<operator>.listLiteral")
      ujson.Obj("k" -> "listE", "items" -> exprs(kids))
    else if (mfn == "<operator>.tupleLiteral")
      ujson.Obj("k" -> "tupleE", "items" -> exprs(kids))
    else if (mfn == "<operator>.dictLiteral")
      // The Python frontend emits `{}` here and fills it with indexed stores; a
      // dictLiteral with children would be a shape we have not seen and must not guess at.
      (if (kids.isEmpty) ujson.Obj("k" -> "dictE", "pairs" -> ujson.Arr())
       else hole("op:dictLiteral-nonempty"))
    else if (mfn.startsWith("<operator>"))
      hole("op:" + mfn.stripPrefix("<operator>."))
    // `import x` / `from p import x`: a binding, not a call. See `importValue`.
    else if (c.name == "import" && mfn == "<unknownFullName>" &&
             (kids match {
               case (_: Identifier) :: (_: Literal) :: (_: Literal) :: Nil => true
               case _                                                     => false
             }))
      importValue(kids(1).asInstanceOf[Literal].code.trim,
                  kids(2).asInstanceOf[Literal].code.trim)
    else {
      // A real call. Arguments are the children with argumentIndex >= 1; the callee sits
      // at -1 and the Python frontend repeats the receiver at 0.
      val args   = kids.filter(aidx(_) >= 1)
      val callee = kids.find(aidx(_) == -1).orElse(kids.headOption)
      // Construction: Joern resolves `Cls(...)` to `...Cls.__init__` while keeping the
      // call's name as the class. An explicit `super().__init__(...)` keeps name
      // `__init__` and is a method call, not an allocation.
      val ctor: Option[String] =
        if (mfn.endsWith(".__init__") && c.name != "__init__") Some(c.name)
        else callee match {
          case Some(i: Identifier) if classNames.contains(i.name) && i.name == c.name => Some(i.name)
          case _                                                                      => None
        }
      // `Cls.<fakeNew>(args)` — the frontend's spelling of allocation inside the metaclass
      // machinery. The receiver at index 0 is the TYPE_REF, so the real arguments start at
      // 1 exactly as for any other call.
      val fakeNew: Option[String] = callee.flatMap(asField).collect {
        case (t: TypeRef, "<fakeNew>") => t.typeFullName.stripSuffix("<meta>").split('.').last
      }
      // `Cls.<body>()` — evaluating a class body *produces the class object*. This is the
      // one shape where an empty call name meant something we can say exactly.
      val classBody: Option[String] = callee.collect {
        case m: MethodRef if m.methodFullName.endsWith(".<body>") =>
          m.methodFullName.stripSuffix(".<body>")
      }
      if (fakeNew.isDefined)
        ujson.Obj("k" -> "alloc", "cls" -> fakeNew.get, "args" -> exprs(args))
      else if (classBody.isDefined) typeValue(classBody.get + "<meta>")
      else ctor match {
        case Some(cls) => ujson.Obj("k" -> "alloc", "cls" -> cls, "args" -> exprs(args))
        case None =>
          callee.flatMap(asField) match {
            case Some((recv, m)) =>
              ujson.Obj("k" -> "mcall", "recv" -> expr(recv), "m" -> m, "args" -> exprs(args))
            // Only a call the frontend left *unnamed* can be one of these; a named call
            // already says what it invokes, and rerouting it on a name coincidence would
            // be a guess.
            case None => (if (c.name.isEmpty) boundMethodCall(c, callee, args) else None)
              .getOrElse {
              // A call with no callee name is not a call we can emit. `Expr.call` is *by
              // name*; there is no "apply this value", so `f(x)(y)` — a callee that is
              // itself computed — has no Core form. Emitting `call ""` (as this did) was
              // worse than a hole: it type-checked, counted as translated, and then
              // resolved to nothing at run time. That is the silently-wrong category the
              // ledger exists to prevent, so it is now a hole that says which shape it was.
              if (c.name.isEmpty)
                hole(if (callee.exists(_.isInstanceOf[Call])) "call:computed-callee"
                     else "call:no-callee-name")
              // Joern often resolves the callee to a method of this program. Emitting that
              // `fullName` rather than the short name is what makes `_wrapper` in
              // `_cached.py` distinguishable from `_wrapper` in `_cachedmethod.py`:
              // `Ctx.resolve` matches the full name exactly, where its short-name fallback
              // needs a *unique* suffix and so resolved neither.
              else if (methodByName.contains(mfn))
                ujson.Obj("k" -> "call", "f" -> mangledFullName(mfn), "args" -> exprs(args))
              else ujson.Obj("k" -> "call", "f" -> c.name, "args" -> exprs(args))
            }
          }
      }
    }
  }

  // ---- statements -----------------------------------------------------------
  def seqOf(xs: List[ujson.Obj]): ujson.Obj =
    if (xs.isEmpty) skip
    else xs.reduceRight((a, b) => ujson.Obj("k" -> "seq", "a" -> a, "b" -> b))

  /** Python's frontend turns statement-expressions (comprehensions, display literals)
    * into a BLOCK whose last child is the value. Split it into prelude statements and
    * the value expression rather than losing it to a hole. */
  def valueOf(n: AstNode): (List[ujson.Obj], ujson.Obj) = n match {
    case b: Block =>
      kidsOf(b) match {
        case Nil  => (Nil, hole("expr:empty-block"))
        case ks   => (ks.init.map(stmt), expr(ks.last))
      }
    case other => (Nil, expr(other))
  }

  /** `for x in e:` — the Python frontend desugars it before we ever see it, into
    *     tmp = e.__iter__()
    *     while <UNKNOWN iteratorNonEmptyOrException>: { x = tmp.__next__(); body }
    * Recovering the `forIn` from that shape is what makes iteration translatable at all;
    * there is no FOR control structure in a Python CPG. */
  def forPattern(kids: List[AstNode]): Option[ujson.Obj] = kids match {
    case (a: Call) :: (w: ControlStructure) :: Nil
        if a.methodFullName == "<operator>.assignment" &&
           (w.controlStructureType == "WHILE" || w.controlStructureType == "DO") =>
      val ak = kidsOf(a)
      val wk = kidsOf(w)
      val iterVar = ak.headOption.collect { case i: Identifier => i.name }
      val condIsIter = wk.headOption.exists { c =>
        c.isInstanceOf[Unknown] && c.code.contains("iteratorNonEmptyOrException")
      }
      // rhs is `X.__iter__()`, possibly wrapped in a block that computes X first.
      def iterSource(rhs: AstNode): Option[(List[ujson.Obj], ujson.Obj)] = rhs match {
        case b: Block =>
          kidsOf(b) match {
            case Nil => None
            case ks  => iterSource(ks.last).map { case (_, e) => (ks.init.map(stmt), e) }
          }
        case c: Call if c.name == "__iter__" =>
          kidsOf(c).find(aidx(_) == -1).flatMap(asField).map { case (r, _) => (Nil, expr(r)) }
        case _ => None
      }
      for {
        tmp  <- iterVar
        if condIsIter && ak.size == 2 && wk.size >= 2
        src  <- iterSource(ak(1))
        body <- wk.lift(1).collect { case b: Block => b }
        bk    = kidsOf(body)
        first<- bk.headOption
        (x, ok) = first match {
          case nx: Call if nx.methodFullName == "<operator>.assignment" =>
            kidsOf(nx) match {
              case (i: Identifier) :: (nc: Call) :: Nil if nc.name == "__next__" =>
                val recvOk = kidsOf(nc).find(aidx(_) == -1).flatMap(asField)
                  .exists { case (r, _) => r.isInstanceOf[Identifier] &&
                                           r.asInstanceOf[Identifier].name == tmp }
                (i.name, recvOk)
              case _ => ("", false)
            }
          case _ => ("", false)
        }
        if ok
      } yield seqOf(src._1 :+ ujson.Obj(
        "k" -> "forIn", "x" -> x, "e" -> src._2, "body" -> seqOf(bk.tail.map(stmt))))
    case _ => None
  }

  /** Assignment, including the augmented forms, to any of the three target shapes. */
  def assignTo(lhs: AstNode, rhs: AstNode, aug: Option[String]): ujson.Obj = {
    val (prelude, rhsE) = valueOf(rhs)
    def combine(cur: => ujson.Obj): ujson.Obj = aug match {
      case None     => rhsE
      case Some(op) => ujson.Obj("k" -> "binop", "op" -> op, "a" -> cur, "b" -> rhsE)
    }
    val core = lhs match {
      // `s += n` on a `char*` advances a pointer; see `cStringUnsafe`. The augmented form
      // never reaches `callExpr`, so it is guarded here too.
      case _ if cLikeFile && aug.isDefined && (isCString(lhs) || isCString(rhs)) =>
        holeS("cstr:pointer-arith")
      case i: Identifier =>
        // At module scope, and for a name a `global` statement rebound, an assignment
        // writes the module-level frame rather than creating a local.
        val k = if (moduleScope || declaredGlobals.contains(i.name)) "setGlobal" else "assign"
        ujson.Obj("k" -> k, "x" -> i.name,
                  "e" -> combine(ujson.Obj("k" -> "name", "v" -> i.name)))
      case fa if asField(fa).isDefined =>
        val (r, f) = asField(fa).get
        if (aug.isDefined && !pureNode(r)) holeS("assign:aug-impure-receiver")
        else ujson.Obj("k" -> "setField", "r" -> expr(r), "f" -> f,
                       "v" -> combine(ujson.Obj("k" -> "field", "a" -> expr(r), "f" -> f)))
      case ia if asIndex(ia).isDefined =>
        val (a, b) = asIndex(ia).get
        if (aug.isDefined && !(pureNode(a) && pureNode(b))) holeS("assign:aug-impure-target")
        else ujson.Obj("k" -> "setIndex", "r" -> expr(a), "i" -> expr(b),
                       "v" -> combine(ujson.Obj("k" -> "index", "a" -> expr(a), "b" -> expr(b))))
      case c: Call if c.methodFullName.startsWith("<operator>") =>
        holeS("assign:lhs:" + c.methodFullName.stripPrefix("<operator>."))
      case other => holeS("assign:lhs:" + other.label)
    }
    seqOf(prelude :+ core)
  }

  /** `global a, b` — the names it rebinds. */
  def globalDeclNames(u: Unknown): List[String] =
    u.code.trim.stripPrefix("global").split(",").map(_.trim).filter(_.nonEmpty).toList

  def stmt(n: AstNode): ujson.Obj = n match {
    case b: Block =>
      val kids = kidsOf(b)
      forPattern(kids).getOrElse(seqOf(kids.map(stmt)))
    case l: Local => skip   // declarations carry no behaviour here
    case r: Return =>
      kidsOf(r).headOption match {
        case Some(e) =>
          val (prelude, ev) = valueOf(e)
          seqOf(prelude :+ ujson.Obj("k" -> "ret", "e" -> ev))
        case None => ujson.Obj("k" -> "ret", "e" -> ujson.Obj("k" -> "unit"))
      }
    case c: Call if c.methodFullName == "<operator>.assignment" =>
      kidsOf(c) match {
        case lhs :: rhs :: Nil => assignTo(lhs, rhs, None)
        case _                 => holeS("assign:arity")
      }
    case c: Call if c.methodFullName == "<operator>.assignmentPlus" ||
                    c.methodFullName == "<operator>.assignmentMinus" =>
      val op = if (c.methodFullName.endsWith("Plus")) "+" else "-"
      kidsOf(c) match {
        case lhs :: rhs :: Nil => assignTo(lhs, rhs, Some(op))
        case _                 => holeS("assign:arity")
      }
    case c: Call if c.methodFullName == "<operator>.pass" => skip
    case c: Call if c.methodFullName == "<operator>.raise" =>
      // Children: the exception, plus an optional `from <e>` cause we do not model.
      kidsOf(c).headOption match {
        case Some(e) => ujson.Obj("k" -> "raise", "e" -> expr(e))
        // A bare `raise` re-raises the exception in flight; Core has no such notion.
        case None    => holeS("op:raise-bare")
      }
    case c: Call if c.methodFullName == "<operator>.delete" =>
      kidsOf(c) match {
        case (i: Identifier) :: Nil => ujson.Obj("k" -> "del", "x" -> i.name)
        // `del d[k]` / `del o.f` remove a binding from a container or object; Core's
        // `del` only unbinds a variable, so translating them would be a lie.
        case (x: AstNode) :: Nil if isOp(x, "<operator>.indexAccess") => holeS("op:delete-index")
        case (x: AstNode) :: Nil if asField(x).isDefined => holeS("op:delete-field")
        case (x: Call) :: Nil if x.methodFullName.startsWith("<operator>") =>
          holeS("op:delete-" + x.methodFullName.stripPrefix("<operator>."))
        case _ => holeS("op:delete-shape")
      }
    case c: Call => ujson.Obj("k" -> "exprS", "e" -> expr(c))
    case cs: ControlStructure =>
      val kids = kidsOf(cs)
      cs.controlStructureType match {
        case "IF" if kids.size >= 2 =>
          ujson.Obj("k" -> "ifte", "c" -> expr(kids(0)), "t" -> stmt(kids(1)),
                    "e" -> (if (kids.size > 2) stmt(kids(2)) else skip))
        case "WHILE" | "DO" if kids.size >= 2 =>
          // A `while` whose condition is the frontend's synthetic iterator probe only
          // makes sense inside the `for` shape above; on its own it is not a condition.
          if (kids(0).isInstanceOf[Unknown]) holeS("control:WHILE-iterator")
          else ujson.Obj("k" -> "loop", "c" -> expr(kids(0)), "body" -> stmt(kids(1)))
        case "BREAK"    => ujson.Obj("k" -> "brk")
        case "CONTINUE" => ujson.Obj("k" -> "cont")
        case "ELSE" | "CATCH" | "FINALLY" => seqOf(kids.map(stmt))
        case "TRY"      => tryStmt(kids)
        case t          => holeS("control:" + t)
      }
    case i: Identifier => ujson.Obj("k" -> "exprS", "e" -> expr(i))
    case l: Literal    => ujson.Obj("k" -> "exprS", "e" -> expr(l))
    case m: MethodRef  => skip   // a nested `def`; its body is exported as its own function
    case t: TypeRef    => skip   // a nested `class`, likewise
    case j: JumpTarget => skip
    // `global x` / `nonlocal x` arrive as UNKNOWN nodes carrying their source text; the
    // Python frontend models neither.
    //
    // `global` *is* representable: it rebinds `x` to the module-level frame, and
    // `declGlobal` records that. (The assignments themselves are independently rewritten
    // to `setGlobal` in `assignTo`, so the translation is correct even if `declGlobal`
    // carries no weight in the semantics.)
    //
    // `nonlocal` is **not**. `Expr.closure` captures the enclosing scope *by value*, so a
    // write can never be observed by the frame that owns the variable. Emitting an
    // `assign` here would produce a program that runs and quietly computes the wrong
    // answer, which is the one outcome worse than a hole.
    case u: Unknown if u.code.trim.startsWith("global ") =>
      seqOf(globalDeclNames(u).map(x => ujson.Obj("k" -> "declGlobal", "x" -> x)))
    case u: Unknown if u.code.trim.startsWith("nonlocal ") =>
      holeS("scope:nonlocal-write")
    case u: Unknown    => holeS("stmt:UNKNOWN:" + u.code.trim.takeWhile(_ != ' '))
    case other         => holeS("stmt:" + other.label)
  }

  /** try / except / else / finally.
    *
    * Note what the CPG does *not* carry: pysrc2cpg drops the exception *type* of each
    * handler entirely (a CATCH has only its body). So a single handler is translated as
    * catch-all — the only reading available — and anything where the choice of handler
    * would be observable stays a hole. */
  def tryStmt(kids: List[AstNode]): ujson.Obj = {
    def of(t: String) = kids.collect {
      case c: ControlStructure if c.controlStructureType == t => c
    }
    val catches   = of("CATCH")
    val finallys  = of("FINALLY")
    val elses     = of("ELSE")
    val bodyNodes = kids.filterNot(_.isInstanceOf[ControlStructure])
    val body      = seqOf(bodyNodes.map(stmt))
    if (bodyNodes.isEmpty) holeS("control:TRY-shape")
    // Which handler runs depends on the exception type, which the CPG discarded.
    else if (catches.size > 1) holeS("control:TRY-multiCatch")
    else {
      // `try: B except: H else: E finally: F` is three independent layers, and now that
      // `Stmt.tryFinally` exists each one has a constructor, so they compose:
      //
      //   inner = B                                    (no handler)
      //         | tryCatch(B, e, H)                     (handler, no else)
      //         | ok = true; tryCatch(B, e, {ok = false; H}); if ok then E
      //   whole = inner | tryFinally(inner, F)
      //
      // The `else` encoding is the only one that needs an explanation. `E` must run only
      // when `B` raised nothing, and `E`'s own exceptions must not reach `H`. The flag is
      // not an invention: it is exactly the "did the body complete normally" bit the
      // construct is about. `E` sits outside the `tryCatch`, so its exceptions propagate;
      // every other way out of `B` — return, break, continue, or a handler that re-raises
      // — leaves before the `if`, which is Python's rule that `else` is skipped whenever
      // the body did not complete normally. The flag is numbered per `try`, because a
      // nested `try/else` completing normally would otherwise re-arm the enclosing one's.
      //
      // `finally` is outermost, which is what makes it run on the `return`/`break`/
      // `continue` paths as well: `Stmt.tryFinally` intercepts every `Ctl`, re-raising the
      // body's outcome after the finalizer unless the finalizer itself leaves abnormally.
      // The previous encoding — `tryCatch(B, e, F; raise e); F` — could not, because `ret`
      // passes straight through a `tryCatch` and would have skipped the trailing copy;
      // that is the whole of what `control:TRY-finally-escaping` was recording.
      val inner =
        if (catches.isEmpty && elses.isEmpty) body
        else if (catches.size == 1 && elses.isEmpty)
          ujson.Obj("k" -> "tryCatch", "body" -> body, "x" -> "__exc",
                    "handler" -> stmt(catches.head))
        else if (catches.size == 1) {
          elseFlagSeq += 1
          val flag = "__else_ok" + elseFlagSeq
          seqOf(List(
            ujson.Obj("k" -> "assign", "x" -> flag,
                      "e" -> ujson.Obj("k" -> "bool", "v" -> true)),
            ujson.Obj("k" -> "tryCatch", "body" -> body, "x" -> "__exc",
                      "handler" -> ujson.Obj("k" -> "seq",
                        "a" -> ujson.Obj("k" -> "assign", "x" -> flag,
                                         "e" -> ujson.Obj("k" -> "bool", "v" -> false)),
                        "b" -> stmt(catches.head))),
            ujson.Obj("k" -> "ifte", "c" -> ujson.Obj("k" -> "name", "v" -> flag),
                      "t" -> seqOf(elses.map(stmt)), "e" -> skip)))
        }
        // `else` with no `except` is not legal Python; if the CPG says so, say so.
        else holeS("control:TRY-else-without-except")
      if (finallys.isEmpty) inner
      else if (finallys.size == 1)
        ujson.Obj("k" -> "tryFinally", "body" -> inner, "fin" -> stmt(finallys.head))
      else holeS("control:TRY-multiFinally")
    }
  }

  // ---- drive ----------------------------------------------------------------
  // Joern synthesises `<metaClassAdapter>` wrappers that duplicate real methods, plus
  // `<body>` class-body pseudo-methods. Counting them inflates every coverage number, so
  // they are excluded rather than quietly padding the verifiable core. The file-level
  // `<module>`/`<global>` pseudo-methods are excluded from *this* list too, and re-added
  // below as initializers, so they never inflate the function count either.
  val cLikeExts = List(".c", ".h", ".cpp", ".cc", ".hpp", ".java", ".js", ".ts", ".kt", ".go")

  /** Translate one method with the right scope/dialect state installed. `isModule` marks
    * the file-level pseudo-method, where every identifier assignment is a global write. */
  def emit(m: Method, isModule: Boolean): ujson.Obj = {
    moduleScope  = isModule
    currentClass = enclosingClassOf(m.fullName)
    cLikeFile    = cLikeExts.exists(e => m.filename.toLowerCase.endsWith(e))
    currentFile  = m.filename
    declaredGlobals =
      m.body.ast.collect { case u: Unknown if u.code.trim.startsWith("global ") => u }
        .flatMap(globalDeclNames).toSet
    // `t = r.attr` for a plain identifier receiver, collected once per method. A name
    // bound more than once is dropped: which binding a later call sees would be a
    // flow-sensitive question, and this analysis is not.
    boundMethods = m.body.ast.isCall
      .filter(_.methodFullName == "<operator>.assignment").l
      .flatMap { a =>
        kidsOf(a) match {
          case (t: Identifier) :: rhs :: Nil =>
            asField(rhs).collect { case (r: Identifier, f) => t.name -> (r.name, f) }
          case _ => None
        }
      }
      .groupBy(_._1).collect { case (k, List(one)) => k -> one._2 }.toMap
    attrsOf = m.body.ast.isCall
      .filter(_.methodFullName == "<operator>.fieldAccess").l
      .flatMap(fa => asField(fa).collect { case (r: Identifier, f) => r.name -> f })
      .groupBy(_._1).map { case (k, vs) => k -> vs.map(_._2).toSet }
    val body = stmt(m.body)
    moduleScope = false
    currentClass = None
    declaredGlobals = Set.empty
    boundMethods = Map.empty
    attrsOf = Map.empty
    val obj = ujson.Obj(
      "name"   -> mangledFullName(m.fullName),
      "file"   -> m.filename,
      "params" -> ujson.Arr.from(m.parameter.name.l.filterNot(_ == "self")),
      "body"   -> body
    )
    // Builtin bases ride on the module *initializer* entry — the function that runs the
    // file's `class` statements — rather than on the methods, so that a builtin-based
    // class with no methods at all is still recorded. The key is optional and absent when
    // empty, which is what keeps every existing AST byte-identical.
    if (isModule) {
      val cb = classBasesByFile.getOrElse(m.filename, Map.empty)
      if (cb.nonEmpty)
        obj("classBases") = ujson.Obj.from(cb.toList.sortBy(_._1).map { case (k, v) =>
          k -> (ujson.Str(v): ujson.Value)
        })
    }
    obj
  }

  // `<metaClassCallHandler>` joins the list §24 left it off. It is generated *per class*
  // and its body is `cls.__init__(<fakeNew>(...))` — the allocation Joern already models
  // at every real construction site — so it is neither user code nor reachable from user
  // code. Counting it inflated both the denominator and the hole-free numerator; excluding
  // it removes padding, not coverage, and the numbers below separate the two.
  val synthetic = List("<metaClassAdapter>", "<metaClassCallHandler>",
                       "<global>", "<body>", "<fakeNew>")
  val methods = cpg.method.isExternal(false)
    .whereNot(_.nameExact("<module>"))
    .l.filterNot(m => synthetic.exists(m.fullName.contains))
    .take(maxMethods)

  // The file-level pseudo-method. It was previously excluded outright, which meant every
  // module-level constant, class and `def` was an unresolvable free name — the single
  // biggest contributor to the call-closure gap. It is now exported as an *initializer*:
  // a zero-argument function whose body is a run of `setGlobal`s establishing the
  // module-level frame. `<global>` is the C frontend's spelling of the same thing.
  val moduleMethods = cpg.method.isExternal(false)
    .l.filter(m => m.name == "<module>" || m.name == "<global>")
    .filterNot(m => m.fullName.contains("<includes>"))
    .sortBy(_.fullName)

  val funcs = methods.map(emit(_, false))
  val inits = moduleMethods.map(emit(_, true))
  val all   = funcs ++ inits

  os.write.over(os.Path(out, os.pwd), ujson.write(ujson.Arr.from(all), indent = 1))

  def countKind(v: ujson.Value, k: String): Int = v match {
    case o: ujson.Obj => (if (o.value.get("k").exists(_.str == k)) 1 else 0) +
                         o.value.values.map(countKind(_, k)).sum
    case a: ujson.Arr => a.value.map(countKind(_, k)).sum
    case _            => 0
  }
  val doc = ujson.Arr.from(all)
  println(s"exported ${funcs.size} functions + ${inits.size} module initializers to $out "
        + s"(${countKind(doc, "closure")} closures, ${countKind(doc, "setGlobal")} global writes)")
}
