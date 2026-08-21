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
-- Modules that cannot join this import graph, and why.
--
-- Every `Autoform/Generated/<M>.lean` defines `Autoform.Generated.program`, so at most
-- ONE generated corpus can be in a single import graph. `Autoform.Overflow` (above)
-- already brings in `Generated.CMath`, which locks the slot: `Autoform/BuiltinBase.lean`,
-- `Autoform/Contracts.lean`, `Autoform/Specs/CachetoolsSpec.lean` and
-- `Autoform/SpecsGen/Cachetools.lean` all need `Generated.Cachetools`, and
-- `Autoform/Specs/V8Spec.lean` needs `Generated.V8Base`.
--
-- Those five are therefore gated by explicit `lake build <module>` steps in
-- `.github/workflows/ci.yml` ("standalone modules elaborate"). That is not a formality:
-- they had ALL stopped elaborating while `lake build` stayed green, because nothing built
-- them and the inventory check counted `theorem` lines with grep. A module no build ever
-- touches will rot, so a module that cannot be imported must be named in CI instead.
-- `Autoform/Specs/CppCastSpec.lean` needs no generated corpus, so it simply joins here.
import Autoform.Specs.CppCastSpec
