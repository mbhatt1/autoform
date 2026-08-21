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
