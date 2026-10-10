package autoform.compiler

/** Stateless neutral-AST constructors and stack-safe serialization. */
object Json {
  def hole(label: String): ujson.Obj  = ujson.Obj("k" -> "hole", "label" -> label)
  def holeS(label: String): ujson.Obj = ujson.Obj("k" -> "holeS", "label" -> label)
  /** Renders a `ujson.Value` to JSON text by driving the same `Renderer`/`Visitor`
    * protocol `ujson.write` itself uses (`ujson.Value$.transform` walks a value and
    * calls exactly these `visitObject`/`visitArray`/`visitString`/... methods), but with
    * an explicit heap-allocated frame stack instead of the JVM call stack -- so output is
    * produced for a chain of any depth without recursing once per nesting level. This is
    * research.md item 3's route (a) (drive the streaming visitor directly): confirmed
    * reachable from a `.sc` script via `ujson.Renderer`'s public constructor and
    * `upickle.core.Visitor`'s public methods (no `ujson.Value` internals needed), and
    * confirmed byte-identical to `ujson.write(v, indent)` for both `indent = 1` and
    * compact (`indent = -1`) on every shape tested, including this exact `seq`-chain
    * shape. `indent = 1` pretty-printing is quadratic in output size at deep nesting
    * (indentation alone is a 1..N space triangle) -- confirmed empirically to
    * OutOfMemoryError a 100,000-deep chain regardless of stack safety -- so the caller
    * passes `indent = -1` once `maxSeqChainLen` crosses `seqChainCompactThreshold`;
    * every already-working (shallow) run keeps `indent = 1` and is therefore still
    * byte-identical to today's output (FR-004). */
  def writeJson(root: ujson.Value, indent: Int): String = {
    val sw = new java.io.StringWriter()
    val renderer = new ujson.Renderer(sw, indent, false)

    sealed trait JsonFrame { var awaitingChild: Boolean = false }
    final case class ArrFrame(ov: upickle.core.ArrVisitor[Any, Any], it: Iterator[ujson.Value])
      extends JsonFrame
    final case class ObjFrame(ov: upickle.core.ObjVisitor[Any, Any], it: Iterator[(String, ujson.Value)])
      extends JsonFrame

    val stack = scala.collection.mutable.ArrayBuffer.empty[JsonFrame]
    var lastResult: AnyRef = null

    def visitScalar(v: upickle.core.Visitor[Any, Any], value: ujson.Value): AnyRef = value match {
      case ujson.Str(s) => v.visitString(s, -1).asInstanceOf[AnyRef]
      case ujson.Num(n) => v.visitFloat64(n, -1).asInstanceOf[AnyRef]
      case ujson.True   => v.visitTrue(-1).asInstanceOf[AnyRef]
      case ujson.False  => v.visitFalse(-1).asInstanceOf[AnyRef]
      case ujson.Null   => v.visitNull(-1).asInstanceOf[AnyRef]
      case other        => throw new IllegalArgumentException(s"writeJson: not a scalar: $other")
    }

    // Pushes a frame for Obj/Arr (their children are visited across later loop
    // iterations, not here) or resolves a scalar immediately into `lastResult`.
    def descend(v: upickle.core.Visitor[Any, Any], value: ujson.Value): Unit = value match {
      case a: ujson.Arr =>
        val ov = v.visitArray(a.value.length, -1).asInstanceOf[upickle.core.ArrVisitor[Any, Any]]
        stack.append(ArrFrame(ov, a.value.iterator))
      case o: ujson.Obj =>
        val ov = v.visitObject(o.value.size, true, -1).asInstanceOf[upickle.core.ObjVisitor[Any, Any]]
        stack.append(ObjFrame(ov, o.value.iterator))
      case scalar =>
        lastResult = visitScalar(v, scalar)
    }

    descend(renderer.asInstanceOf[upickle.core.Visitor[Any, Any]], root)
    while (stack.nonEmpty) {
      stack.last match {
        case af: ArrFrame =>
          // `awaitingChild` is true when we come back around to this frame after a
          // previously-pushed child (however many levels it itself descended) finally
          // unwound -- its result must reach `visitValue` before asking for the next item.
          if (af.awaitingChild) { af.ov.visitValue(lastResult, -1); af.awaitingChild = false }
          if (af.it.hasNext) {
            val sub = af.ov.subVisitor.asInstanceOf[upickle.core.Visitor[Any, Any]]
            af.awaitingChild = true
            descend(sub, af.it.next())
            // A scalar child resolves in the same iteration (no frame was pushed);
            // consume it right away instead of waiting for a loop iteration that will
            // never come back to a still-scalar "child".
            if (stack.last eq af) { af.ov.visitValue(lastResult, -1); af.awaitingChild = false }
          } else {
            lastResult = af.ov.visitEnd(-1).asInstanceOf[AnyRef]
            stack.remove(stack.length - 1)
          }
        case of: ObjFrame =>
          if (of.awaitingChild) { of.ov.visitValue(lastResult, -1); of.awaitingChild = false }
          if (of.it.hasNext) {
            val (k, value) = of.it.next()
            val kv = of.ov.visitKey(-1).asInstanceOf[upickle.core.Visitor[Any, Any]]
            of.ov.visitKeyValue(kv.visitString(k, -1))
            val sub = of.ov.subVisitor.asInstanceOf[upickle.core.Visitor[Any, Any]]
            of.awaitingChild = true
            descend(sub, value)
            if (stack.last eq of) { of.ov.visitValue(lastResult, -1); of.awaitingChild = false }
          } else {
            lastResult = of.ov.visitEnd(-1).asInstanceOf[AnyRef]
            stack.remove(stack.length - 1)
          }
      }
    }
    renderer.flushCharBuilder()
    sw.toString
  }
  // Iterative for the same reason `writeJson` is: `all` may contain a "seq" chain as
  // deep as `maxSeqChainLen`, and this walk is our own code, not `ujson`'s -- a plain
  // self-recursive version (as this was before) would overflow the JVM stack right after
  // the write above succeeds, on the very inputs this feature exists to fix.
  def countKind(v: ujson.Value, k: String): Int = {
    var total = 0
    val work = scala.collection.mutable.ArrayBuffer.empty[ujson.Value]
    work.append(v)
    while (work.nonEmpty) {
      work.remove(work.length - 1) match {
        case o: ujson.Obj =>
          if (o.value.get("k").exists(_.str == k)) total += 1
          o.value.values.foreach(work.append(_))
        case a: ujson.Arr =>
          a.value.foreach(work.append(_))
        case _ => ()
      }
    }
    total
  }
}
