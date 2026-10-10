import Autoform.Lang.Imp.Syntax
import Autoform.Lang.Imp.Semantics
import Autoform.Lang.PCode.Semantics
import Autoform.Lang.PCode.Properties
import Autoform.Harness.Audit
import Autoform.Lang.Core.Syntax
import Autoform.Lang.Core.Semantics
import Autoform.Lang.Core.Observation
import Autoform.Lang.Core.ExcSafe
import Autoform.Ledger
import Autoform.Harness.Conformance
import Autoform.Tactics.Portfolio
import Autoform.Refine
import Autoform.Overflow
import Autoform.FuelMono
import Autoform.CallingConvention
import Autoform.SpecsGen.Basis
import Autoform.NL.Basis
import Autoform.BuiltinBase
import Autoform.Contracts
import Autoform.Specs.CachetoolsSpec
import Autoform.SpecsGen.Cachetools
import Autoform.Specs.V8Spec
import Autoform.SpecsGen.V8BaseSample
import Autoform.SpecsGen.LinuxLib
import Autoform.SpecsGen.LinuxLibSample
import Autoform.Specs.CppCastSpec
import Autoform.Specs.DoWhileSpec

/-!
# `Autoform.CI` — the import closure the CI build job elaborates

`Autoform.lean` is the whole project, including `Autoform.SpecsGen.V8Base`: 74 part modules
of by-computation proofs whose heaviest parts hold more memory than a 16 GB GitHub runner
has (locally the merged build peaks near 25 GB on a single spec module). On the runner that
job died with SIGTERM partway through the parts, every time, and a build that cannot
finish gates nothing. This umbrella is `Autoform.lean` minus that one import; the CI build
and the trust audit (`scripts/audit_all.py --strict --module Autoform.CI`, including
`leanchecker --fresh`) run on it. `Autoform.SpecsGen.V8Base` stays gated by
`scripts/check_specs.py` and by the release checklist (`docs/releasing.md`), which runs the
full `lake build` on a machine that can. Keep the two import lists in step: a module added
to `Autoform.lean` belongs here too unless it is a V8Base-sized proof module, in which case
say so there.
-/
