import Autoform.Lang.Imp.Syntax
import Autoform.Lang.Imp.Semantics
import Autoform.Harness.Audit
import Autoform.Lang.Core.Syntax
import Autoform.Lang.Core.Semantics
import Autoform.Ledger
import Autoform.Harness.Conformance
import Autoform.Tactics.Portfolio
import Autoform.Refine
import Autoform.Overflow
import Autoform.FuelMono
import Autoform.CallingConvention

-- The synthesised specification modules. These were NOT in the build until this merge,
-- and the omission was not cosmetic: `lake build` was green, `audit_all.py` printed PASS,
-- and CI counted `theorem` lines with grep -- while `Autoform/SpecsGen/Cachetools.lean`,
-- the home of the repository's 79 headline theorems, had not elaborated since
-- `Autoform/SpecsGen/Basis.lean` changed shape under it. A proof nobody runs is a
-- claim, not a proof; grep is not an oracle. Importing them here puts every theorem in
-- them through the kernel on every build, and through `leanchecker` in the audit.
import Autoform.SpecsGen.Basis

-- ---------------------------------------------------------------------------
-- Every module in the repository is now in this graph.
--
-- Until today each `Autoform/Generated/<M>.lean` declared `namespace Autoform.Generated`
-- and defined `program` inside it, so importing two generated corpora failed outright:
-- "environment already contains 'Autoform.Generated.program'". At most one corpus could
-- be in any single import graph, and `Autoform.Overflow` (above) took the slot with
-- `Generated.CMath`. That is why `Autoform/BuiltinBase.lean`, `Autoform/Contracts.lean`,
-- `Autoform/Specs/CachetoolsSpec.lean`, `Autoform/SpecsGen/Cachetools.lean` and
-- `Autoform/Specs/V8Spec.lean` sat outside this file, gated by a separate CI step -- and
-- therefore outside `leanchecker --fresh`, which replays only what is reachable from
-- `Autoform`.
--
-- `cartographer/render_lean.py` now emits `namespace Autoform.Generated.<Module>`, so the
-- programs are `Autoform.Generated.Cachetools.program`, `Autoform.Generated.V8Base.program`
-- and so on, and any number of corpora coexist. The consequence below is the one this
-- change existed for: theorems about cachetools (Python) and theorems about V8 (C++) are
-- in ONE build, kernel-checked together, replayed together by `leanchecker --fresh`.
import Autoform.BuiltinBase
import Autoform.Contracts
import Autoform.Specs.CachetoolsSpec
import Autoform.SpecsGen.Cachetools
import Autoform.Specs.V8Spec
import Autoform.SpecsGen.V8BaseSample
import Autoform.SpecsGen.LinuxLib
import Autoform.SpecsGen.LinuxLibSample
import Autoform.Specs.CppCastSpec

-- V8 `src/base` laws: 73 modules, with the shared context and all 73 domains in
-- `V8Base.Base`. One Lean process retains every `rfl` term it elaborates, and each of
-- these evaluates the interpreter over a domain against a 1,920-function program; 63 in
-- one module reached 15.3 GB after 76 minutes without finishing, and every part was also
-- re-proving `C_tfFree`, an `rfl` over all 1,920 bodies. Split plus a shared base builds
-- 73/73 in about ten minutes.
import Autoform.SpecsGen.V8Base
import Autoform.Specs.DoWhileSpec

-- ---------------------------------------------------------------------------
-- The one module still outside this graph, and why.
--
-- `Autoform/SpecsGen/V8Base.lean` (229 synthesised laws over the 1,920-function V8 base
-- corpus) is NOT here, and the reason is no longer the namespace collision this change
-- removed -- `Autoform.Specs.V8Spec`, which imports the same `Generated.V8Base`, is in
-- the graph two lines above. The reason is elaboration cost: a single `lean` process on
-- that file ran past 57 minutes of CPU and 16 GB of RSS without finishing (see
-- `scripts/check_specs.py`, which exists for exactly this module and has always recorded
-- it as not proving). Importing it would make every `lake build` in the repository
-- unbounded, so it stays gated behind `scripts/check_specs.py V8Base` until its laws are
-- regenerated in a form that elaborates. Its CI inventory floor is a floor on TEXT and
-- says so; do not read it as a proof count.
