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

  /** `e.f` — a fieldAccess is [receiver, FIELD_IDENTIFIER], except that when the Python
    * frontend has *resolved* the attribute it prepends the resolved METHOD_REF/TYPE_REF,
    * giving [METHOD_REF, receiver, FIELD_IDENTIFIER]. */
  def asField(n: AstNode): Option[(AstNode, String)] = n match {
    case c: Call if c.methodFullName == "<operator>.fieldAccess" =>
      val k = kidsOf(c)
      k.lastOption match {
        case Some(f: FieldIdentifier) if k.size >= 2 => Some((k(k.size - 2), f.canonicalName))
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

  /** A function value that reads a variable of an enclosing function is a *closure*;
    * one that does not is an `fnref`, which is cheaper and needs no captured frame. */
  val capturesEnv: Map[String, Boolean] = allMethods.map { m =>
    m.fullName -> freeOf(m.fullName).intersect(enclosingFunctionBindings(m.fullName)).nonEmpty
  }.toMap

  def fnValue(target: String): ujson.Obj =
    if (capturesEnv.getOrElse(target, false)) ujson.Obj("k" -> "closure", "f" -> target)
    else ujson.Obj("k" -> "fnref", "v" -> target)

  /** A class used as a value. Usually an `fnref` — but a class *defined inside a
    * function* whose methods read that function's variables is a capturing value too, and
    * `Expr.closure` names a function, not a class, so there is nothing to emit. Rather
    * than hand back an `fnref` whose methods would later find those names unbound, say so. */
  def typeValue(target: String): ujson.Obj = {
    val cls = target.stripSuffix("<meta>")
    val captures = allMethods.exists(m =>
      m.fullName.startsWith(cls + ".") && capturesEnv.getOrElse(m.fullName, false))
    if (captures) hole("scope:class-closure") else ujson.Obj("k" -> "fnref", "v" -> target)
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
    case other                => hole("expr:" + other.label)
  }

  def exprs(ns: List[AstNode]): ujson.Arr = ujson.Arr.from(ns.map(expr))

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
      ctor match {
        case Some(cls) => ujson.Obj("k" -> "alloc", "cls" -> cls, "args" -> exprs(args))
        case None =>
          callee.flatMap(asField) match {
            case Some((recv, m)) =>
              ujson.Obj("k" -> "mcall", "recv" -> expr(recv), "m" -> m, "args" -> exprs(args))
            case None =>
              ujson.Obj("k" -> "call", "f" -> c.name, "args" -> exprs(args))
          }
      }
    }
  }

  // ---- statements -----------------------------------------------------------
  def seqOf(xs: List[ujson.Obj]): ujson.Obj =
    if (xs.isEmpty) skip
    else xs.reduceRight((a, b) => ujson.Obj("k" -> "seq", "a" -> a, "b" -> b))

  /** Does this statement transfer control out of its enclosing block? Used to decide
    * whether a `finally` can be duplicated safely. Conservative: any occurrence counts. */
  def escapes(o: ujson.Value): Boolean = o match {
    case obj: ujson.Obj =>
      val k = obj.value.get("k").map(_.str).getOrElse("")
      k == "ret" || k == "brk" || k == "cont" || obj.value.values.exists(escapes)
    case arr: ujson.Arr => arr.value.exists(escapes)
    case _              => false
  }

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
    // `else` runs only when the body did not raise, and its own exceptions must not be
    // caught. Neither is expressible with one tryCatch.
    else if (elses.nonEmpty) holeS("control:TRY-else")
    // Which handler runs depends on the exception type, which the CPG discarded.
    else if (catches.size > 1) holeS("control:TRY-multiCatch")
    else if (catches.size == 1 && finallys.isEmpty)
      ujson.Obj("k" -> "tryCatch", "body" -> body, "x" -> "__exc",
                "handler" -> stmt(catches.head))
    else if (catches.isEmpty && finallys.size == 1) {
      // `try: B finally: F` == `tryCatch(B, e, F; raise e); F` — F runs exactly once on
      // both paths — but only when B cannot leave by return/break/continue, since those
      // escape the tryCatch and would skip the trailing copy.
      val fin = stmt(finallys.head)
      if (escapes(body) || escapes(fin)) holeS("control:TRY-finally-escaping")
      else
        ujson.Obj("k" -> "seq",
          "a" -> ujson.Obj("k" -> "tryCatch", "body" -> body, "x" -> "__exc",
                           "handler" -> ujson.Obj("k" -> "seq", "a" -> fin,
                             "b" -> ujson.Obj("k" -> "raise",
                                              "e" -> ujson.Obj("k" -> "name", "v" -> "__exc")))),
          "b" -> fin)
    }
    else holeS("control:TRY-catch-and-finally")
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
    moduleScope = isModule
    cLikeFile   = cLikeExts.exists(e => m.filename.toLowerCase.endsWith(e))
    declaredGlobals =
      m.body.ast.collect { case u: Unknown if u.code.trim.startsWith("global ") => u }
        .flatMap(globalDeclNames).toSet
    val body = stmt(m.body)
    moduleScope = false
    declaredGlobals = Set.empty
    ujson.Obj(
      "name"   -> m.fullName,
      "file"   -> m.filename,
      "params" -> ujson.Arr.from(m.parameter.name.l.filterNot(_ == "self")),
      "body"   -> body
    )
  }

  val synthetic = List("<metaClassAdapter>", "<global>", "<body>", "<fakeNew>")
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
