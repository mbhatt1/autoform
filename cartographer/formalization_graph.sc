// Joern query: emit the formalization graph for a codebase.
//
// This is Layer 1 (Cartographer). It is a *query over a bought index*, not a tool we
// wrote: Joern builds the code property graph (AST + CFG + PDG + call graph) across
// C/C++/Java/JS/Python/Kotlin/binary, and we ask it three questions.
//
//   1. What is the call graph?        -> topological order for the work queue
//   2. What is the effect class?      -> which constructs become `Stmt.opaqueHole`
//   3. What is the formalizability?   -> scoring, hence the budget/ordering policy
//
// Run:  joern --script cartographer/formalization_graph.sc --param cpgPath=/path/to/cpg.bin
//
// The scoring weights below ARE the policy, and the policy is the part that is ours.

import io.shiftleft.codepropertygraph.generated.nodes.Method
import scala.collection.mutable

@main def exec(cpgPath: String, out: String = "formalization-graph.json") = {
  importCpg(cpgPath)

  // --- Effect boundary taxonomy -------------------------------------------------
  // Anything matching these becomes a tracked hole rather than a silent omission.
  val effectPatterns = Map(
    "io"          -> List("open", "read", "write", "print", "recv", "send", "socket"),
    "ffi"         -> List("dlopen", "ctypes", "jni", "extern", "unsafe"),
    "reflection"  -> List("eval", "exec", "getattr", "setattr", "reflect", "Class.forName"),
    "concurrency" -> List("thread", "spawn", "async", "await", "mutex", "lock"),
    "nondeterm"   -> List("random", "time", "now", "uuid", "getenv")
  )

  def effectsOf(m: Method): List[String] = {
    val callees = m.call.code.l.mkString(" ").toLowerCase
    effectPatterns.collect {
      case (cls, pats) if pats.exists(callees.contains) => cls
    }.toList
  }

  // --- Formalizability score ----------------------------------------------------
  // Higher = formalize earlier. Leaves of the call graph with no effects come first;
  // the frontier then grows outward. This ordering is the whole point of Layer 1.
  def score(m: Method, fanout: Int, effects: List[String]): Double = {
    val loc      = m.numberOfLines
    val branches = m.controlStructure.size
    val base     = 100.0
    base -
      (effects.size * 25.0) -      // each effect class is a hole we must assume away
      (fanout * 2.0) -             // depends on much = formalize its dependencies first
      (loc * 0.1) -                // size is proportional to proof burden
      (branches * 1.5)             // control complexity dominates the case analysis
  }

  val methods = cpg.method.isExternal(false).l
  val rows = methods.map { m =>
    val callees = m.callee.fullName.dedup.l
    val effects = effectsOf(m)
    ujson.Obj(
      "name"            -> m.fullName,
      "file"            -> m.filename,
      "line"            -> m.lineNumber.getOrElse(0).toString,
      "loc"             -> m.numberOfLines,
      "branches"        -> m.controlStructure.size,
      "callees"         -> ujson.Arr.from(callees),
      "fanout"          -> callees.size,
      "effects"         -> ujson.Arr.from(effects),
      "pure"            -> effects.isEmpty,
      "formalizability" -> score(m, callees.size, effects)
    )
  }

  val sorted = rows.sortBy(r => -r("formalizability").num)
  os.write.over(os.Path(out, os.pwd), ujson.write(ujson.Arr.from(sorted), indent = 2))
  println(s"wrote ${sorted.size} methods to $out")
  println(s"pure leaves (work-queue head): ${rows.count(r => r("pure").bool && r("fanout").num == 0)}")
}
