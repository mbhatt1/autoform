// Joern query: finish a CPG parsed with `--nooverlays`, without the dataflow overlay.
//
// A fallback, used only when the default `joern-parse` has failed in its `dataflowOss`
// overlay. On real Kotlin repositories kotlin2cpg itself succeeds and the crash comes
// after it, in ReachingDefPass (`NoSuchElementException: key not found: ...MethodRef`);
// joern-parse then exits 1 and the whole run is lost. Measured on five real Kotlin
// packages: three crashed this way, and one of them exported 0 functions before this
// script and 177 after it.
//
// Parsing with `--nooverlays` alone is not enough: `importCpg` in `export_ast.sc` (and
// in `formalization_graph.sc`) re-applies every default overlay the CPG does not list as
// applied, and so crashes in the same pass. Here the CPG is imported with
// `enhance = false`, the overlays the exporter does read are applied in their default
// order (base: AST and type declarations; controlflow: CFG, dominators; typerelations;
// callgraph), and `dataflowOss` is recorded in `metaData.overlays` as applied, so the
// later `importCpg` leaves the graph alone. That record is the one untrue thing in the
// output; it is safe because nothing under `cartographer/compiler/` reads a dataflow
// edge (no REACHING_DEF, no `reachableBy`). The caller says it skipped the overlay in
// its own records (parse.log, pipeline.json, pr.json's `exporter`).
//
// Run: joern-parse <src> --nooverlays --output raw.bin
//      joern --script cartographer/prepare_cpg.sc --param cpgPath=raw.bin --param out=cpg.bin

import flatgraph.DiffGraphApplier
import io.shiftleft.codepropertygraph.generated.Cpg

@main def exec(cpgPath: String, out: String) = {
  importCpg(cpgPath, enhance = false)
  run.base
  run.controlflow
  run.typerelations
  run.callgraph
  val md = cpg.metaData.head
  if (!md.overlays.contains("dataflowOss")) {
    val diff = Cpg.newDiffGraphBuilder
    diff.setNodeProperty(md, "OVERLAYS", md.overlays :+ "dataflowOss")
    DiffGraphApplier.applyDiff(cpg.graph, diff)
  }
  flatgraph.storage.Serialization.writeGraph(cpg.graph, java.nio.file.Paths.get(out))
  // The callers grep for this line: no line, no prepared CPG.
  println("prepared cpg without dataflowOss; overlays: " + cpg.metaData.head.overlays.mkString(","))
}
