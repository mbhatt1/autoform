import Autoform.Overflow
import Autoform.Generated.CMath
open Autoform.Core Autoform.Overflow Autoform.Generated
#eval (analyzeFunc f_poly).conds
#eval (analyzeFunc f_poly).complete
#eval (analyzeFunc f_cdiv).conds
#eval (analyzeFunc f_cdiv).complete
#eval (analyzeFunc f_clamp).conds
#eval (analyzeFunc f_clamp).complete
#eval (analyzeFunc f_cmod).conds
#eval (analyzeFunc f_sumto).complete
