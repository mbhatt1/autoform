import Autoform.Refine
import Autoform.Generated.Cachetools
namespace Autoform.Specs.Probe
open Autoform.Core Autoform.Refine
abbrev P : Program := Autoform.Generated.program
open Autoform.Generated in
#eval runFunc P 20 "cachetools/__init__.py:<module>._TimedCache.expire" [.int 3]
open Autoform.Generated in
#eval (applyFunc (ctxOf P) 20 [{cls := "Cache", fields := [("_Cache__data", .dict [(.int 1, .int 9)])]}]
        f_cachetools___init___py__module__Cache___contains__ (some (.ref 0)) [.int 1]).2
open Autoform.Generated in
#eval (applyFunc (ctxOf P) 20 [{cls := "T", fields := [("_Timer__nesting", .int 5)]}]
        f_cachetools___init___py__module___TimedCache__Timer___exit__ (some (.ref 0)) [.unit])
end Autoform.Specs.Probe
