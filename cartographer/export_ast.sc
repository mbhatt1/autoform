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

  /** `++`/`--`, and which way they go. In *statement* position all four are `x = x ± 1`
    * and nothing distinguishes prefix from postfix — the value is discarded. In
    * *expression* position they differ and neither is expressible, so `callExpr` holes
    * them under a `:value` label. Keeping the two positions apart is the whole point:
    * `for (i = 0; i < n; i++)` is translatable, `a[i++]` is not. */
  val incrOps = Map(
    "<operator>.preIncrement" -> "+", "<operator>.postIncrement" -> "+",
    "<operator>.preDecrement" -> "-", "<operator>.postDecrement" -> "-"
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

  /** The two CPG spellings of "select a field of something".
    *
    * C and C++ distinguish `o.f` (`fieldAccess`) from `p->f` (`indirectFieldAccess`), and
    * Joern keeps the distinction. **Core does not need it.** A `Val.ref` *is* the object,
    * so `Expr.field` on a ref already looks the field up in the heap object it names;
    * `p->f` and `(*p).f` are the same expression, and both are `Expr.field`. The C++
    * frontend gives `indirectFieldAccess` exactly the shape `fieldAccess` has —
    * `[pointerExpr, FIELD_IDENTIFIER]` — so this is a *mapping* gap, not a semantics gap,
    * and closing it is one line here rather than a constructor in `Syntax.lean`.
    *
    * Same story for `p[i]`: `indirectIndexAccess` has `indexAccess`'s shape and
    * `Expr.index`'s meaning. (What `Expr.index` then *does* with a C array is a separate
    * question, and the answer is an honest `index:unsupported` hole at run time — the
    * array itself has no Core value. The mapping is still the right one: it puts the
    * ignorance on the array, where it belongs, instead of on the subscript syntax.) */
  val fieldOps = Set("<operator>.fieldAccess", "<operator>.indirectFieldAccess")
  val indexOps = Set("<operator>.indexAccess", "<operator>.indirectIndexAccess")

  /** `e.f` — a fieldAccess is [receiver, FIELD_IDENTIFIER], except that when the Python
    * frontend has *resolved* the attribute it prepends the resolved METHOD_REF/TYPE_REF,
    * giving [METHOD_REF, receiver, FIELD_IDENTIFIER]. */
  def asField(n: AstNode): Option[(AstNode, String)] = n match {
    case c: Call if fieldOps.contains(c.methodFullName) =>
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
    case c: Call if fieldOps.contains(c.methodFullName) =>
      kidsOf(c) match {
        case (m: MethodRef) :: _ :: _ :: Nil => Some(m)
        case (t: TypeRef) :: _ :: _ :: Nil   => Some(t)
        case _                               => None
      }
    case _ => None
  }

  /** `e[i]`. */
  def asIndex(n: AstNode): Option[(AstNode, AstNode)] = n match {
    case c: Call if indexOps.contains(c.methodFullName) =>
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
    case c: Call if fieldOps.contains(c.methodFullName) =>
      asField(c).exists(p => pureNode(p._1))
    case c: Call if indexOps.contains(c.methodFullName) =>
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

  /** `moduleAt`, tolerating the package prefix the parse root already stands for.
    *
    * An absolute import names a module by its *installed* path: `from ansible.errors
    * import AnsibleError`. But a CPG is built from a directory, and that directory is
    * usually the package itself — parse `ansible/lib/ansible` and `ansible.errors` lives
    * at `errors.py`, not `ansible/errors.py`. `moduleAt` therefore missed every
    * first-party absolute import and reported it `import:unresolved`, which on Ansible was
    * 3,550 holes — the single largest category in the corpus, and not a language gap at
    * all.
    *
    * So: try the path as given, then try dropping leading segments one at a time. Only a
    * module that actually exists in this CPG can match, and a shorter path is tried only
    * after every longer one has failed, so this cannot prefer a wrong module over a right
    * one. It CAN match a same-named module from a different package if the real target is
    * absent from the CPG — a genuine risk, and the reason the resolved name is recorded
    * rather than assumed. */
  def moduleAtTolerant(path: String): Option[String] = {
    val segs = path.split('/').filter(_.nonEmpty).toList
    (0 until segs.length).view
      .map(i => moduleAt(segs.drop(i).mkString("/")))
      .collectFirst { case Some(m) => m }
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
  /** C and C++ specifically, as opposed to the whole `cLike` *dialect* family (which
    * includes Java, Go, JS, TS and Kotlin). The constructor spelling `Cls::Cls`, the
    * implicit `this`, and stack object construction are C++ facts, not `cLike` facts. */
  var cppFile         = false
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
  /** The type Joern *wrote on the node*, which for C is very often `ANY`. */
  def nodeType(x: AstNode): String = x match {
    case c: Call              => c.typeFullName
    case i: Identifier        => i.typeFullName
    case l: Literal           => l.typeFullName
    case p: MethodParameterIn => p.typeFullName
    case t: TypeRef           => t.typeFullName
    case _                    => ""
  }

  /** Declared types of the locals and parameters of the method being translated. */
  var localTypes = Map.empty[String, String]

  /** Names this method selects a field off with `.`, and names it selects one off with
    * `->`. C's two spellings are a *syntactic* proof of what the name holds: `x.f`
    * cannot be written unless `x` is an aggregate, and `p->f` cannot be written unless
    * `p` is a pointer. Nothing else in the CPG says this as reliably — Joern's C frontend
    * leaves 2,848 of `lib/`'s address-taken identifiers typed `ANY` and absent from the
    * LOCAL table — and it is derived from the code rather than from type recovery, so it
    * cannot be defeated by a missing header. */
  var valueReceivers = Set.empty[String]
  var ptrReceivers   = Set.empty[String]

  /** `(owning type, member name) -> member type`, for the whole program. */
  lazy val memberTypes: Map[(String, String), String] =
    cpg.typeDecl.l.flatMap { td =>
      td.member.l.map(mm => (bareType(td.fullName), mm.name) -> mm.typeFullName)
    }.toMap

  /** The static type of an expression, **recovered from declarations when the node does
    * not carry one**.
    *
    * This is not a nicety. Measured on Linux `lib/`, 2,849 of 3,145 `&x` sites had
    * operand type `ANY` on the node — the C frontend simply does not propagate types onto
    * IDENTIFIER nodes — and `ANY` is the one answer that decides nothing: it cannot say
    * whether `&x` is the address of a struct (which Core represents, because a `Val.ref`
    * *is* an address) or the address of an `int` (which it does not). The declaration is
    * right there in the same method, on the LOCAL node, and the field's type is right
    * there on the owning TypeDecl's MEMBER.
    *
    * So the ledger's largest label was in large part a *type-recovery* gap masquerading
    * as a semantics gap. That is worth stating precisely, because the two have completely
    * different remedies and only one of them is expensive. */
  def staticTypeOf(x: AstNode): String = {
    val direct = nodeType(x)
    if (direct.nonEmpty && direct != "ANY") direct
    else x match {
      case i: Identifier => localTypes.getOrElse(i.name, direct)
      case c: Call if fieldOps.contains(c.methodFullName) =>
        asField(c).flatMap { case (r, f) =>
          // `p->f` and `o.f` are one node kind here, so strip any pointer depth off the
          // receiver's type before looking the member up on the owning declaration.
          val owner = bareType(staticTypeOf(r)).reverse.dropWhile(_ == '*').reverse
          memberTypes.get((owner, f))
        }.getOrElse(direct)
      // `*p` has the type `p` points to.
      case c: Call if c.methodFullName == "<operator>.indirection" =>
        kidsOf(c) match {
          case k :: Nil =>
            val t = bareType(staticTypeOf(k))
            if (t.endsWith("*")) t.dropRight(1) else direct
          case _ => direct
        }
      case _ => direct
    }
  }

  def isCString(n: AstNode): Boolean = {
    val ty = staticTypeOf(n).replace(" ", "")
    ty.matches("""(const|volatile|signed|unsigned)*char(\*|\[.*\]).*""")
  }

  // ---- C and C++ types ------------------------------------------------------
  //
  // Everything below is about telling apart three things that C spells with much the same
  // syntax: a **number**, a **pointer**, and an **object**. Core models the first and the
  // third; it has no model of an address at all. So each pointer-shaped construct is
  // routed by what its operand's static type says, and the ones that land on "address"
  // keep a hole whose label says *which* address shape it was.

  /** Strip cv-qualifiers and whitespace, so `const unsigned char *` compares equal to
    * `unsigned char*`. */
  def bareType(ty: String): String =
    ty.replace("const ", "").replace("volatile ", "")
      .replace("struct ", "").replace("union ", "").replace("enum ", "")
      .replace(" ", "")

  /** A pointer or an array — a value Core cannot represent, because it is an address.
    * `char[311]` is one of these: an array decays to a pointer. */
  def isPointerType(ty: String): Boolean = {
    val b = bareType(ty)
    b.endsWith("*") || b.matches(""".*\[.*\]""") || b == "std.nullptr_t"
  }

  /** The fixed-width integer types, mapped to the width tag `applyUnop` understands.
    * `size_t`/`uintptr_t` are here because they are integers on the platform the oracle
    * measures, not because they are portable. */
  val intTypeNames: Map[String, String] = Map(
    "int8_t" -> "i8", "signedchar" -> "i8",
    "uint8_t" -> "u8", "unsignedchar" -> "u8",
    "int16_t" -> "i16", "short" -> "i16", "shortint" -> "i16",
    "uint16_t" -> "u16", "unsignedshort" -> "u16",
    "int32_t" -> "i32", "int" -> "i32", "signedint" -> "i32", "long" -> "i32",
    "uint32_t" -> "u32", "unsignedint" -> "u32", "unsigned" -> "u32",
    "int64_t" -> "i64", "longlong" -> "i64", "ptrdiff_t" -> "i64",
    "uint64_t" -> "u64", "unsignedlonglong" -> "u64", "size_t" -> "u64",
    "uintptr_t" -> "u64"
  )

  /** `char` is deliberately absent from `intTypeNames`: its signedness is
    * implementation-defined, so `static_cast<char>(300)` has no standard-mandated value.
    * Naming it separately keeps the hole label specific instead of guessing a sign. */
  def isArithType(ty: String): Boolean = intTypeNames.contains(bareType(ty))

  /** Aggregates — struct, union, class — for which the CPG carries **positive
    * evidence**: a TypeDecl that has members, or (C++) one that has methods.
    *
    * The test has to be positive. The tempting rule is "not a pointer and not a number,
    * therefore a struct", and it is wrong in the dangerous direction: `loff_t`, `s64` and
    * every other kernel scalar typedef would pass it, and `&some_s64` would then
    * translate to the identity — a well-typed program silently aliasing a number as an
    * object. That is the exact failure mode this ledger exists to prevent, so a type we
    * merely *cannot classify* gets its own hole label (`opaque-type`) rather than the
    * benefit of the doubt. */
  lazy val aggregateNames: Set[String] = {
    val ds = cpg.typeDecl.l.filter(td => td.member.nonEmpty || td.method.nonEmpty)
    (ds.map(_.fullName) ++ ds.map(_.name)).map(bareType).toSet ++ fieldOwnerTypes
  }

  /** Types the *program itself* selects a field off. `x.f` or `p->f` is a proof that `x`
    * is an aggregate that no type table is needed to supply, and on the kernel it is the
    * evidence that actually exists: Joern records 4,892 TypeDecls for `lib/` but members
    * for only 753 of them, so a members-only test calls most real structs unknown.
    * Field selection is derived from the code, not from the frontend's type recovery,
    * which is exactly why it survives where the type table does not. */
  lazy val fieldOwnerTypes: Set[String] =
    cpg.call.l.filter(c => fieldOps.contains(c.methodFullName)).flatMap { c =>
      val ks = c.astChildren.collect { case a: AstNode => a }.l
      if (ks.size < 2) None
      else {
        val t = bareType(nodeType(ks(ks.size - 2)))
        val bare = t.reverse.dropWhile(_ == '*').reverse
        if (bare.isEmpty || bare == "ANY") None else Some(bare)
      }
    }.toSet

  val nonClassScalars = Set("ANY", "void", "bool", "char", "float", "double", "")

  /** Kernel and C scalar typedefs beyond `intTypeNames`, named so that `&x` on one of
    * them is reported as `scalar` (a location model would fix it) rather than as
    * `opaque-type` (better types would fix it). */
  val scalarTypedefs = Set(
    "s8", "s16", "s32", "s64", "u8", "u16", "u32", "u64", "loff_t", "ssize_t",
    "off_t", "gfp_t", "pid_t", "uid_t", "gid_t", "dev_t", "sector_t", "phys_addr_t",
    "dma_addr_t", "resource_size_t", "cycles_t", "ktime_t", "wchar_t", "intptr_t",
    "longdouble", "signedlong", "unsignedlong", "longunsigned", "int128_t", "__u8",
    "__u16", "__u32", "__u64", "__s8", "__s16", "__s32", "__s64", "__be16", "__be32",
    "__be64", "__le16", "__le32", "__le64", "bool_t", "size_type"
  )

  /** The type is an aggregate, so `&it` is the identity: a Core class instance already
    * *is* a heap address, and taking its address changes nothing. */
  def isClassType(ty: String): Boolean = {
    val raw = ty.replace("const ", "").replace("volatile ", "").trim
    val b   = bareType(ty)
    if (isPointerType(b) || isArithType(b) || nonClassScalars.contains(b) ||
        scalarTypedefs.contains(b)) false
    // Joern's C frontend spells the tag in the type name (`unioncodetag_ref`), which is
    // conclusive evidence on its own.
    else raw.startsWith("struct") || raw.startsWith("union") || raw.startsWith("class") ||
         aggregateNames.contains(b)
  }

  /** A hole label naming what kind of address defeated us, so the ledger separates
    * "pointer to a number" (which needs a location model) from "we could not tell"
    * (which needs better types). */
  /** What *shape* of thing had its address taken. The kind (below) says what Core would
    * need in order to represent the pointee; the shape says which of four distinct pieces
    * of work would close the case, and they are not the same piece of work:
    *
    *   * `local`   — the address of a variable. Needs a model of a variable's *location*.
    *   * `field`   — `&p->f`. Free for an object-typed field (a `Val.ref` already is its
    *                 own address); needs a location for a scalar one.
    *   * `element` — `&a[i]`. Needs arrays as heap objects, and then interior pointers.
    *   * `call`    — `&f(...)`, or an address taken of something computed. Rare.
    *
    * Reporting them merged is what made `op:addressOf` look like one problem. */
  def addrShape(n: AstNode): String = n match {
    case _: Identifier | _: MethodParameterIn => "local"
    case c: Call if fieldOps.contains(c.methodFullName) => "field"
    case c: Call if indexOps.contains(c.methodFullName) => "element"
    case _: Call => "call"
    case other   => other.label.toLowerCase
  }

  def addrKind(ty: String): String = {
    val b = bareType(ty)
    if (b.isEmpty || b == "ANY")   "unknown-type"
    else if (isPointerType(b))     "pointer"
    else if (isClassType(ty))      "object"
    else if (isArithType(b) || scalarTypedefs.contains(b) ||
             nonClassScalars.contains(b))  "scalar"
    // A name, but no evidence for what is behind it. This is a *type* gap, not a
    // semantics gap, and it is closed by a better frontend rather than by a location
    // model — which is why it must not be filed under either of the other two.
    else                           "opaque-type"
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
      moduleAtTolerant(path) match {
        case None => hole("import:unresolved")
        case Some(mod) =>
          val target = mod + "." + name
          if (methodByName.contains(target))        fnValue(target)
          else if (classByFullName.contains(target)) typeValue(target + "<meta>")
          // `from . import keys` where `keys` is a sibling *module*, not a member.
          else if (moduleAtTolerant(path + "/" + name).isDefined) hole("import:module-value")
          else hole("import:unresolved")
      }
    }
  }

  /** C++'s receiver is spelled `this`; Core's — the name `applyFunc` binds a method's
    * receiver to — is `self`. Without this rename `this->f` translated to a read of an
    * unbound name, which is the vacuous outcome: an `Expr.field` on `unit`, holing at run
    * time for a reason that had nothing to do with pointers. The rename is what makes the
    * `indirectFieldAccess` mapping actually reach a heap object. */
  def localName(n: String): String = if (cppFile && n == "this") "self" else n

  // ---- expressions ----------------------------------------------------------
  /** Parse a C/C++/Java integer literal.
    *
    * `toIntOption` alone was the whole implementation, and on V8 it failed on 309 of the
    * literals in `src/base` — every hex constant, every `u`/`U`/`L`/`ULL` suffix, C++14
    * digit separators (`0x0010'0000'0000'0000`), binary `0b10000`, and anything past
    * 2^31. Each became a `lit:unquoted` hole, so a function containing `0xFFFFFFFF` was
    * unanalysable for want of a number.
    *
    * Returns `BigInt` because a C++ literal routinely exceeds `Int` and often exceeds
    * `Long` (`0xFFFFFFFFFFFFFFFF`). The caller emits anything beyond 2^53 as a decimal
    * *string*, since JSON numbers are doubles and would silently round it — the exact
    * class of quiet corruption this project keeps finding.
    */
  def parseIntLiteral(raw: String): Option[BigInt] = {
    var t = raw.trim.replace("'", "")            // C++14 digit separators
    if (t.isEmpty) return None
    var neg = false
    if (t.startsWith("-")) { neg = true; t = t.drop(1) }
    else if (t.startsWith("+")) t = t.drop(1)
    // Integer suffixes, in any order and case: 0u, 1L, 2ULL, 3llu.
    val body = t.reverse.dropWhile(ch => ch == 'u' || ch == 'U' || ch == 'l' || ch == 'L').reverse
    if (body.isEmpty) return None
    val parsed: Option[BigInt] =
      try {
        if (body.length > 2 && (body.startsWith("0x") || body.startsWith("0X")))
          Some(BigInt(body.drop(2), 16))
        else if (body.length > 2 && (body.startsWith("0b") || body.startsWith("0B")))
          Some(BigInt(body.drop(2), 2))
        // A leading zero is octal in C, but plain "0" is zero, and a decimal point or an
        // exponent means this is a float and not ours to claim.
        else if (body.length > 1 && body.head == '0' && body.forall(_.isDigit))
          Some(BigInt(body.drop(1), 8))
        else if (body.forall(_.isDigit)) Some(BigInt(body))
        else None
      } catch { case _: NumberFormatException => None }
    parsed.map(v => if (neg) -v else v)
  }

  /** JSON for an integer literal, without losing precision to a double. */
  def intLit(v: BigInt): ujson.Obj =
    if (v.abs <= BigInt(2).pow(53)) ujson.Obj("k" -> "int", "v" -> v.toLong)
    else ujson.Obj("k" -> "int", "v" -> v.toString)

  def expr(n: AstNode): ujson.Obj = n match {
    case l: Literal =>
      val c0 = l.code.trim
      // String-literal prefixes: L"x" (wide), u8"x", u"x", U"x". The prefix selects an
      // encoding Core does not model; the *content* is what the program uses, and
      // dropping the prefix is exactly what `unquoted` already does for the quotes.
      val c =
        if (c0.length >= 3 && (c0.startsWith("L\"") || c0.startsWith("u\"") || c0.startsWith("U\""))) c0.drop(1)
        else if (c0.length >= 4 && c0.startsWith("u8\"")) c0.drop(2)
        else c0
      val unquoted =
        if (c.length >= 2 && (c.head == '"' || c.head == '\'')) c.drop(1).dropRight(1) else c
      parseIntLiteral(c) match {
        case Some(i) => intLit(i)
        case None =>
          if (c == "True" || c == "true")        ujson.Obj("k" -> "bool", "v" -> true)
          else if (c == "False" || c == "false") ujson.Obj("k" -> "bool", "v" -> false)
          // `nullptr` is not a number and not a string: it is the absence of an object,
          // and `Val.unit` is the one value Core has that no `Val.ref` is equal to. That
          // makes `p == nullptr` answer `false` for every allocated object, which is the
          // right answer, and `Val.unit` for a *dereferenced* null is not reachable
          // because dereference is itself a hole.
          else if (c == "None" || c == "null" || c == "nil" || c == "nullptr")
            ujson.Obj("k" -> "unit")
          // A float is not a string. Core has no floats, so this is a hole, not a lie.
          // Float forms, including the C/C++ `f`/`F`/`l`/`L` suffix and exponent-only
          // spellings (`1e300`). These were falling through to `lit:unquoted`, which
          // reported a *parsing* failure for something we simply do not model yet —
          // wrong label, wrong remedy. `Autoform/Lang/Core/Float.lean` models IEEE-754,
          // so emitting `Lit.float` here is real pending work, not a permanent hole.
          else if (c.matches("""[-+]?(\d+\.\d*|\.\d+|\d+)([eE][-+]?\d+)?[fFlL]?""") &&
                   c.exists(ch => ch == '.' || ch == 'e' || ch == 'E'))
            hole("lit:float")
          // Joern synthesises `<global>` as a namespace marker. It is not a literal the
          // source contains, and counting it as an unparsed one overstated the literal
          // problem roughly tenfold on V8.
          else if (c == "<global>") hole("lit:joern-synthetic")
          else if (c.headOption.exists(ch => ch == '"' || ch == '\''))
            ujson.Obj("k" -> "str", "v" -> unquoted)
          else if (c.isEmpty) ujson.Obj("k" -> "unit")
          // A bare dotted identifier in literal position is not a literal at all: the
          // Python frontend synthesises these as the *operands of import statements*
          // (`__future__`, `annotations`, `ansible.errors`, `typing`, `os`). Filing them
          // under `lit:unquoted` reported a literal-parsing problem and pointed at the
          // wrong remedy -- on Ansible it hid 2,157 import operands inside a label that
          // says "we could not read this number". Naming them `import:operand` puts them
          // with the other import holes, where the actual work is.
          else if (c.matches("""[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*""") ||
                   c == ".")
            hole("import:operand")
          // Unquoted, non-numeric, non-identifier literal code. Calling it a string would
          // be inventing a value.
          else hole("lit:unquoted")
      }
    case i: Identifier        => ujson.Obj("k" -> "name", "v" -> localName(i.name))
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

  /** The class a C++ constructor call names, if it names one.
    *
    * Joern spells a constructor's `methodFullName` as `<qualified class>.<name>:<sig>`,
    * so `v8.internal.NumberParseIntHelper.NumberParseIntHelper:void(ANY,int)` is a
    * constructor exactly when the last two dotted segments agree. `ANY.ANY:void()` agrees
    * too and names nothing, and `int64_t.int64_t:void(int)` — the frontend's spelling of
    * `int64_t{1}` — names a *number*, not a class; both are rejected, because an
    * `Expr.alloc` of either would be a heap object standing in for something that is not
    * one. */
  def ctorClassOf(c: Call): Option[String] = {
    val segs = c.methodFullName.takeWhile(_ != ':').split('.').filter(_.nonEmpty).toList
    segs.reverse match {
      case n :: p :: _ if n == p && n != "ANY" && !intTypeNames.contains(bareType(n)) &&
                          !nonClassScalars.contains(n) => Some(n)
      case _ => None
    }
  }

  /** C++ stack object construction: `Foo x(a, b);`.
    *
    * The frontend lowers it to three siblings —
    *
    *     <tmp>0 = <operator>.alloc
    *     Foo.Foo(a, b)
    *     <tmp>0
    *
    * — which is `Expr.alloc "Foo" [a, b]` and nothing else. Reading it as three
    * independent statements produced an `op:alloc` hole for a construct Core has had a
    * constructor for since the beginning; this is the second-largest purely-exporter gap
    * in the C++ ledger after `p->f`.
    *
    * The constructor *body* is reached because `emit` exports a C++ constructor under the
    * name `__init__`, which is the name `evalExpr`'s `.alloc` case looks for. Without that
    * the object would be allocated with no fields and every later `p->f` would read
    * `unit` — allocated, well-typed, and silently empty. */
  def ctorAlloc(ks: List[AstNode]): Option[ujson.Obj] = ks match {
    case (asg: Call) :: (ctor: Call) :: (last: Identifier) :: Nil
        if asg.methodFullName == "<operator>.assignment" =>
      for {
        (tgt, rhs) <- kidsOf(asg) match {
                        case (i: Identifier) :: r :: Nil => Some((i, r))
                        case _                           => None
                      }
        if tgt.name == last.name
        if isOp(rhs, "<operator>.alloc") && kidsOf(rhs).isEmpty
        cls <- ctorClassOf(ctor)
      } yield ujson.Obj("k" -> "alloc", "cls" -> cls,
                        "args" -> exprs(kidsOf(ctor).filter(aidx(_) >= 1)))
    case _ => None
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
    else if (ctorAlloc(ks).isDefined) ctorAlloc(ks).get
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
    else if (indexOps.contains(mfn) && kids.size == 2)
      ujson.Obj("k" -> "index", "a" -> expr(kids(0)), "b" -> expr(kids(1)))
    else if (fieldOps.contains(mfn))
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
    // `static_cast<uint8_t>(e)` — a **width conversion**, which Core does model.
    //
    // `Autoform/Lang/Core/Numeric.lean` already has `Width`/`IntType`/`IntType.wrap`, and
    // C++20 fixed the one thing that used to make this implementation-defined: conversion
    // to a narrower integer type is two's-complement truncation, which is exactly
    // `IntType.wrap`. So the cast becomes a unary operator `cast:u8` (see `applyUnop`),
    // and `static_cast<uint8_t>(300)` is `44` in Core as it is under `cc`.
    //
    // A **pointer** cast is a different thing wearing the same syntax and is not
    // collapsed into it: reinterpreting an address has no meaning in a language with no
    // addresses. `char` is excluded too — its signedness is implementation-defined — and
    // so is `double`, which is a rounding conversion rather than a truncation.
    else if (mfn == "<operator>.cast" && kids.size == 2)
      intTypeNames.get(bareType(staticTypeOf(kids(0)))) match {
        case Some(w) => ujson.Obj("k" -> "unop", "op" -> ("cast:" + w),
                                  "a" -> expr(kids(1)))
        case None    => hole("op:cast:" + addrKind(staticTypeOf(kids(0))))
      }
    // `&x`.
    //
    // This is the one place where the honest answer depends on what is being addressed,
    // because Core's object model already *is* a pointer model for objects and is not one
    // for anything else:
    //
    //   * `&obj` where `obj` has class type is the identity. A Core class instance is a
    //     `Val.ref` — a heap address — so the address of an object is the object's own
    //     value, and writing through the result mutates the same heap cell. Nothing is
    //     invented and nothing is lost. (What is *not* modelled, and was not before, is
    //     C++ value semantics for such an object: `Foo a = b;` copies in C++ and aliases
    //     in Core. That is a pre-existing Core gap, recorded here rather than introduced.)
    //
    //   * `&n` where `n` is a local number, or `&p` where `p` is a local pointer, needs a
    //     model of *the location of a variable*, which Core does not have. The standard
    //     fix is to box address-taken locals into heap cells, and it is implementable
    //     entirely in this file — but see `docs/pointers.md`: measured on this corpus,
    //     every such local holds a `char*`, so the box would be faithful and its
    //     *contents* would still be an address Core cannot represent. Boxing would buy a
    //     well-typed program that computes nothing. It stays a hole, with the kind of
    //     address named.
    else if (mfn == "<operator>.addressOf" && kids.size == 1) {
      val ty   = staticTypeOf(kids(0))
      val kind = addrKind(ty)
      val nm   = kids(0) match { case i: Identifier => Some(i.name); case _ => None }
      // `&x` on an aggregate is the identity — see the long note below. When the type is
      // unrecovered, `x.f` elsewhere in the same method is proof of the same thing, and
      // `x->f` is proof of the opposite.
      val aggregate =
        isClassType(ty) ||
        (kind == "unknown-type" &&
         nm.exists(n => valueReceivers.contains(n) && !ptrReceivers.contains(n)))
      if (aggregate) expr(kids(0))
      else {
        val k = if (kind == "unknown-type" && nm.exists(ptrReceivers.contains)) "pointer"
                else kind
        hole("op:addressOf:" + addrShape(kids(0)) + ":" + k)
      }
    }
    // `*p`. The dual of the above, and the same split — but the *identity* half is
    // already covered, because Joern spells `(*p).f` as `indirectFieldAccess` and `p[i]`
    // as `indirectIndexAccess`, both of which are now mapped. What reaches here is a
    // dereference whose result is a *number* (or another pointer), which is exactly the
    // location model Core lacks.
    else if (mfn == "<operator>.indirection" && kids.size == 1)
      hole("op:indirection:" + addrKind(staticTypeOf(kids(0))))
    // `++x` / `x++` in **expression** position. In statement position these are
    // `x = x ± 1` and are translated as such (see `stmt`); as an expression they also
    // have a value, and for the postfix forms that value is the *old* one. Core has no
    // way to sequence a write before a read inside an expression, so this is a hole —
    // and it is a different hole from the statement form, which is why the label says
    // `:value`.
    else if (incrOps.contains(mfn))
      hole("op:" + mfn.stripPrefix("<operator>.") + ":value")
    // `<operator>.alloc` with children is a **stack array declaration** (`char b[N]`),
    // not a `new`. Core has no arrays and no sizes, so it stays a hole — but under a
    // label that says which of the two it was, because they are not the same problem.
    // The childless form is C++ stack object construction and is handled as a whole
    // block by `ctorAlloc`; reaching it here means the block did not have that shape.
    else if (mfn == "<operator>.alloc")
      hole(if (kids.isEmpty) "op:alloc:ctor-shape" else "op:alloc:array-decl")
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
      val all = kidsOf(b)
      // C++ stack construction reaches here whenever the constructed object is the value
      // of an assignment, an argument or a `return`, which is most of the time. Splitting
      // it into "two statements and an identifier" is what made `Expr.alloc` unreachable:
      // the pieces are individually meaningless and the middle one is the constructor.
      ctorAlloc(all) match {
        case Some(a) => (Nil, a)
        case None =>
          all match {
            case Nil  => (Nil, hole("expr:empty-block"))
            case ks   => (stmts(ks.init), expr(ks.last))
          }
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
        ujson.Obj("k" -> k, "x" -> localName(i.name),
                  "e" -> combine(ujson.Obj("k" -> "name", "v" -> localName(i.name))))
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

  /** `++x` / `x++` / `--x` / `x--` as a **statement**.
    *
    * With the value discarded, all four are `x = x ± 1`, and prefix and postfix are
    * indistinguishable — this is the ordinary desugaring, not an approximation.
    *
    * Two things it refuses. A **pointer** target is not `p = p + 1`: C scales by
    * `sizeof(*p)`, Core has no sizes, and `p + 1` on a `char*` is only accidentally right
    * (`sizeof(char) == 1`). Writing the accidental case and holing the rest would put a
    * silent type dependency into the translation, so every pointer target holes — the
    * same rule `cstr:pointer-arith` already applies to `p += n`. And an **impure**
    * target holes, because the desugaring evaluates the target twice; that is
    * `assign:aug-impure-*`'s rule, applied here for the same reason. */
  def incrStmt(tgt: AstNode, op: String, opName: String): ujson.Obj = {
    val one = ujson.Obj("k" -> "int", "v" -> ujson.Num(1.0))
    def bump(cur: ujson.Obj): ujson.Obj =
      ujson.Obj("k" -> "binop", "op" -> op, "a" -> cur, "b" -> one)
    if (isPointerType(staticTypeOf(tgt)) || isCString(tgt)) holeS("op:" + opName + ":pointer")
    else tgt match {
      case i: Identifier =>
        val k = if (moduleScope || declaredGlobals.contains(i.name)) "setGlobal" else "assign"
        ujson.Obj("k" -> k, "x" -> localName(i.name),
                  "e" -> bump(ujson.Obj("k" -> "name", "v" -> localName(i.name))))
      case fa if asField(fa).isDefined =>
        val (r, f) = asField(fa).get
        if (!pureNode(r)) holeS("op:" + opName + ":impure-receiver")
        else ujson.Obj("k" -> "setField", "r" -> expr(r), "f" -> f,
                       "v" -> bump(ujson.Obj("k" -> "field", "a" -> expr(r), "f" -> f)))
      case ia if asIndex(ia).isDefined =>
        val (a, b) = asIndex(ia).get
        if (!(pureNode(a) && pureNode(b))) holeS("op:" + opName + ":impure-target")
        else ujson.Obj("k" -> "setIndex", "r" -> expr(a), "i" -> expr(b),
                       "v" -> bump(ujson.Obj("k" -> "index", "a" -> expr(a), "b" -> expr(b))))
      // `++*p` — the target is a dereference, which is the location model Core lacks.
      case _ => holeS("op:" + opName + ":unsupported-target")
    }
  }

  /** Translate a statement list, merging the two-statement C++ stack-construction shape
    * (`x = <operator>.alloc` followed by `Cls.Cls(args)`) into one `Expr.alloc`. See
    * `ctorAlloc` for the expression-position form of the same pattern. */
  def stmts(ks: List[AstNode]): List[ujson.Obj] = ks match {
    case (asg: Call) :: (ctor: Call) :: rest if asg.methodFullName == "<operator>.assignment" =>
      val merged =
        for {
          tr  <- kidsOf(asg) match {
                   case (i: Identifier) :: r :: Nil => Some((i, r))
                   case _                           => None
                 }
          if isOp(tr._2, "<operator>.alloc") && kidsOf(tr._2).isEmpty
          cls <- ctorClassOf(ctor)
        } yield {
          val k = if (moduleScope || declaredGlobals.contains(tr._1.name)) "setGlobal"
                  else "assign"
          ujson.Obj("k" -> k, "x" -> localName(tr._1.name),
                    "e" -> ujson.Obj("k" -> "alloc", "cls" -> cls,
                                     "args" -> exprs(kidsOf(ctor).filter(aidx(_) >= 1))))
        }
      merged match {
        case Some(m) => m :: stmts(rest)
        case None    => stmt(asg) :: stmts(ctor :: rest)
      }
    case k :: rest => stmt(k) :: stmts(rest)
    case Nil       => Nil
  }

  def stmt(n: AstNode): ujson.Obj = n match {
    case b: Block =>
      val kids = kidsOf(b)
      forPattern(kids).getOrElse(seqOf(stmts(kids)))
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
    case c: Call if incrOps.contains(c.methodFullName) =>
      kidsOf(c) match {
        case tgt :: Nil =>
          incrStmt(tgt, incrOps(c.methodFullName),
                   c.methodFullName.stripPrefix("<operator>."))
        case _ => holeS("op:" + c.methodFullName.stripPrefix("<operator>.") + ":arity")
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
    // A `namespace v8 { ... }` is a *naming* construct: it has no runtime effect at all,
    // and the functions and classes inside it are exported as their own entries with
    // their qualified names already on them. Nothing is dropped by skipping it — the
    // block itself never had behaviour to drop. This is the same call `case m: MethodRef`
    // and `case t: TypeRef` already make one line below.
    case nb: NamespaceBlock => skip
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
  val cppExts   = List(".c", ".h", ".cpp", ".cc", ".hpp")

  /** The name a method is exported under.
    *
    * For C++ this rewrites a **constructor** — whose `fullName` repeats the class, as in
    * `v8.internal.SimpleStringBuilder.SimpleStringBuilder:void(char*,int)` — to
    * `v8.internal.SimpleStringBuilder.__init__`. That is not cosmetic: `evalExpr`'s
    * `.alloc` case runs `ctx.resolveMethod cls "__init__"` and nothing else, so without
    * the rewrite every `Expr.alloc` produced by `ctorAlloc` would allocate an object with
    * no fields, and every subsequent `p->f` would read `unit`. Core's constructor
    * convention is Python's spelling of a universal idea; this is the C++ spelling of the
    * same one, and naming them alike is what makes the two frontends share a semantics.
    *
    * Java's `<init>` and Kotlin's are *not* caught by this rule (their last two segments
    * differ), which is deliberate — they have their own conventions and no evidence here. */
  def exportName(m: Method): String = {
    val fn = mangledFullName(m.fullName)
    if (!cppFile) fn
    else {
      val base = fn.takeWhile(_ != ':')
      val segs = base.split('.').filter(_.nonEmpty).toList
      segs.reverse match {
        case n :: p :: _ if n == p && n != "ANY" => segs.dropRight(1).mkString(".") + ".__init__"
        case _                                   => fn
      }
    }
  }

  /** Translate one method with the right scope/dialect state installed. `isModule` marks
    * the file-level pseudo-method, where every identifier assignment is a global write. */
  def emit(m: Method, isModule: Boolean): ujson.Obj = {
    moduleScope  = isModule
    currentClass = enclosingClassOf(m.fullName)
    cLikeFile    = cLikeExts.exists(e => m.filename.toLowerCase.endsWith(e))
    cppFile      = cppExts.exists(e => m.filename.toLowerCase.endsWith(e))
    def fieldReceiverNames(op: String): Set[String] =
      m.body.ast.isCall.filter(_.methodFullName == op).l.flatMap { c =>
        val ks = kidsOf(c)
        if (ks.size < 2) None else Some(ks(ks.size - 2))
      }.collect { case i: Identifier => i.name }.toSet
    valueReceivers = fieldReceiverNames("<operator>.fieldAccess")
    ptrReceivers   = fieldReceiverNames("<operator>.indirectFieldAccess")
    localTypes   = (m.local.l.map(l => l.name -> l.typeFullName) ++
                    m.parameter.l.map(pp => pp.name -> pp.typeFullName))
                   .filter(_._2 != "ANY").toMap
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
      .filter(c => fieldOps.contains(c.methodFullName)).l
      .flatMap(fa => asField(fa).collect { case (r: Identifier, f) => r.name -> f })
      .groupBy(_._1).map { case (k, vs) => k -> vs.map(_._2).toSet }
    val body = stmt(m.body)
    moduleScope = false
    localTypes = Map.empty
    valueReceivers = Set.empty
    ptrReceivers = Set.empty
    currentClass = None
    declaredGlobals = Set.empty
    boundMethods = Map.empty
    attrsOf = Map.empty
    val obj = ujson.Obj(
      "name"   -> exportName(m),
      "file"   -> m.filename,
      // `this` leaves the parameter list for the same reason `self` does: `applyFunc`
      // binds the receiver itself, under the name the body now uses.
      "params" -> ujson.Arr.from(
        m.parameter.name.l.filterNot(x => x == "self" || (cppFile && x == "this"))),
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
