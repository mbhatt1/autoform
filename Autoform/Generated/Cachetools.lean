import Autoform.Lang.Core.Semantics

-- Lean's default `maxRecDepth` (512) is a guard against runaway elaboration, not
-- a statement about reasonable programs. A deep-embedded function body is one
-- term, so the elaborator's recursion depth tracks the *source's* nesting depth:
-- Linux `lib/` hit the limit at two declarations and the whole module failed to
-- type-check. Raising it costs nothing for shallow modules and is the difference
-- between compiling a real codebase and not.
--
-- 8000 was not enough either. The binding constraint is not the nesting depth of
-- any one body (Ansible's deepest is 297) but the `funcs := [...]` list literal,
-- which elaborates as nested cons cells -- one frame or more per function, and
-- Ansible has 5,546. So the limit has to scale with the module's function count,
-- not with how deep its code happens to be.
set_option maxRecDepth 9672

-- Lean's default `maxHeartbeats` (200000) budgets ONE declaration's own
-- elaboration cost, separately from `maxRecDepth` above (which bounds nesting
-- depth, not total work). A single source file whose top-level declarations
-- carry a large static table -- SQLite's `test_vdbecov.c`, whose `<global>`
-- initializer alone is ~5.3M characters of generated Lean -- blows through the
-- default budget on that ONE declaration and fails with a `(deterministic)
-- timeout at isDefEq` error, unrelated to whether the translation is correct.
-- Unlike `maxRecDepth`, this does not scale with function COUNT (Ansible-style
-- corpora with thousands of small functions never hit it); it is one
-- pathologically large declaration, which no per-function-count formula would
-- predict, so this disables the budget outright rather than guessing a bigger
-- number that the next large static table would just exceed again. Scoped to
-- THIS generated file only (`set_option` here does not touch hand-written proof
-- files elsewhere in the project, which keep the default as a real safety net
-- against a genuine runaway elaboration bug while someone is editing them).
set_option maxHeartbeats 0

/-!
# Cachetools — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.Cachetools
open Autoform.Core

/-- `cachetools/__init__.py:<module>._DefaultSize.__getitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___DefaultSize___getitem__ : Func :=
  { name := "cachetools/__init__.py:<module>._DefaultSize.__getitem__"
  , params := ["_key"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["_key"], isMethod := some true }
  , body := (.ret (.lit (.int 1))) }

/-- `cachetools/__init__.py:<module>._DefaultSize.__setitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___DefaultSize___setitem__ : Func :=
  { name := "cachetools/__init__.py:<module>._DefaultSize.__setitem__"
  , params := ["_key", "_value"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["_key", "_value"], isMethod := some true }
  , body := .skip }

/-- `cachetools/__init__.py:<module>._DefaultSize.pop`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___DefaultSize_pop : Func :=
  { name := "cachetools/__init__.py:<module>._DefaultSize.pop"
  , params := ["_key"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["_key"], isMethod := some true }
  , body := (.ret (.lit (.int 1))) }

/-- `cachetools/__init__.py:<module>._DefaultSize.clear`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___DefaultSize_clear : Func :=
  { name := "cachetools/__init__.py:<module>._DefaultSize.clear"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := .skip }

/-- `cachetools/__init__.py:<module>.Cache.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.__init__"
  , params := ["maxsize", "getsizeof"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["maxsize"], isMethod := some true, defaults := [("getsizeof", (.lit .unit))] }
  , body := (.seq
            (.ifte
              (.name "getsizeof")
              (.setField (.name "self") "getsizeof" (.name "getsizeof"))
              .skip)
            (.seq
              (.ifte
                (.isOp
                  true
                  (.field (.name "self") "getsizeof")
                  (.field (.field (.name "<module>cachetools/__init__.py") "Cache") "getsizeof"))
                (.seq
                  (.assign "tmp0" (.dictE []))
                  (.setField (.name "self") "_Cache__size" (.name "tmp0")))
                .skip)
              (.seq
                (.seq
                  (.assign "tmp1" (.dictE []))
                  (.setField (.name "self") "_Cache__data" (.name "tmp1")))
                (.seq
                  (.setField (.name "self") "_Cache__currsize" (.lit (.int 0)))
                  (.seq
                    (.setField (.name "self") "_Cache__maxsize" (.name "maxsize"))
                    (.seq .skip (.seq .skip .skip))))))) }

/-- `cachetools/__init__.py:<module>.Cache.__repr__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache___repr__ : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.__repr__"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.ret
              (.binop
                "%"
                (.lit (.str "%s(%s, maxsize=%r, currsize=%r)"))
                (.tupleE
                  [ (.field (.call "type" [(.name "self")]) "__name__")
                  , (.call "repr" [(.field (.name "self") "_Cache__data")])
                  , (.field (.name "self") "_Cache__maxsize")
                  , (.field (.name "self") "_Cache__currsize") ])))
            (.seq .skip .skip)) }

/-- `cachetools/__init__.py:<module>.Cache.__getitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache___getitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.__getitem__"
  , params := ["key"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true }
  , body := (.tryCatch
            (.ret (.index (.field (.name "self") "_Cache__data") (.name "key")))
            "$exprV$168"
            (.ifte
              (.inOp false (.name "$exprV$168") (.tupleE [(.lit (.str "KeyError"))]))
              (.ret (.mcall (.name "self") "__missing__" [(.name "key")]))
              (.raise (.name "$exprV$168")))) }

/-- `cachetools/__init__.py:<module>.Cache.__setitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache___setitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.__setitem__"
  , params := ["key", "value"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key", "value"], isMethod := some true }
  , body := (.seq
            (.assign "maxsize" (.field (.name "self") "_Cache__maxsize"))
            (.seq
              .skip
              (.seq
                (.assign "size" (.mcall (.name "self") "getsizeof" [(.name "value")]))
                (.seq
                  .skip
                  (.seq
                    (.ifte
                      (.binop "<" (.name "size") (.lit (.int 0)))
                      (.raise
                        (.unop
                          "py:exception:ValueError"
                          (.tupleE [(.lit (.str "value size must be non-negative"))])))
                      .skip)
                    (.seq
                      .skip
                      (.seq
                        (.ifte
                          (.binop ">" (.name "size") (.name "maxsize"))
                          (.raise
                            (.unop
                              "py:exception:ValueError"
                              (.tupleE [(.lit (.str "value too large"))])))
                          .skip)
                        (.seq
                          .skip
                          (.seq
                            (.ifte
                              (.inOp true (.name "key") (.field (.name "self") "_Cache__data"))
                              (.seq
                                (.assign "diffsize" (.name "size"))
                                (.loop
                                  (.binop
                                    ">"
                                    (.binop
                                      "+"
                                      (.field (.name "self") "_Cache__currsize")
                                      (.name "diffsize"))
                                    (.name "maxsize"))
                                  (.expr (.mcall (.name "self") "popitem" []))))
                              (.seq
                                (.assign
                                  "diffsize"
                                  (.binop
                                    "-"
                                    (.name "size")
                                    (.index (.field (.name "self") "_Cache__size") (.name "key"))))
                                (.loop
                                  (.binop
                                    ">"
                                    (.binop
                                      "+"
                                      (.field (.name "self") "_Cache__currsize")
                                      (.name "diffsize"))
                                    (.name "maxsize"))
                                  (.seq
                                    (.expr (.mcall (.name "self") "popitem" []))
                                    (.ifte
                                      (.inOp
                                        true
                                        (.name "key")
                                        (.field (.name "self") "_Cache__data"))
                                      (.assign "diffsize" (.name "size"))
                                      .skip)))))
                            (.seq
                              (.setIndex
                                (.field (.name "self") "_Cache__data")
                                (.name "key")
                                (.name "value"))
                              (.seq
                                (.setIndex
                                  (.field (.name "self") "_Cache__size")
                                  (.name "key")
                                  (.name "size"))
                                (.setField
                                  (.name "self")
                                  "_Cache__currsize"
                                  (.binop
                                    "+"
                                    (.field (.name "self") "_Cache__currsize")
                                    (.name "diffsize")))))))))))))) }

/-- `cachetools/__init__.py:<module>.Cache.__delitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache___delitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.__delitem__"
  , params := ["key"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true }
  , body := (.seq
            (.seq
              (.assign "tmp0" (.field (.name "self") "_Cache__size"))
              (.assign "size" (.mcall (.name "tmp0") "pop" [(.name "key")])))
            (.seq
              .skip
              (.seq
                (.delIndex (.field (.name "self") "_Cache__data") (.name "key"))
                (.seq
                  .skip
                  (.setField
                    (.name "self")
                    "_Cache__currsize"
                    (.binop "-" (.field (.name "self") "_Cache__currsize") (.name "size"))))))) }

/-- `cachetools/__init__.py:<module>.Cache.__contains__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache___contains__ : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.__contains__"
  , params := ["key"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true }
  , body := (.ret (.inOp false (.name "key") (.field (.name "self") "_Cache__data"))) }

/-- `cachetools/__init__.py:<module>.Cache.__missing__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache___missing__ : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.__missing__"
  , params := ["key"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true }
  , body := (.seq (.raise (.unop "py:exception:KeyError" (.tupleE [(.name "key")]))) .skip) }

/-- `cachetools/__init__.py:<module>.Cache.__iter__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache___iter__ : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.__iter__"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq (.ret (.call "iter" [(.field (.name "self") "_Cache__data")])) .skip) }

/-- `cachetools/__init__.py:<module>.Cache.__len__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache___len__ : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.__len__"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq (.ret (.call "len" [(.field (.name "self") "_Cache__data")])) .skip) }

/-- `cachetools/__init__.py:<module>.Cache.get`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache_get : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.get"
  , params := ["key", "default"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true, defaults := [("default", (.lit .unit))] }
  , body := (.ifte
            (.inOp false (.name "key") (.name "self"))
            (.ret (.index (.name "self") (.name "key")))
            (.ret (.name "default"))) }

/-- `cachetools/__init__.py:<module>.Cache.pop`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache_pop : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.pop"
  , params := ["key", "default"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true, classAttrDefaults := [("default", "cachetools/__init__.py:<module>.Cache", "_Cache__marker")] }
  , body := (.seq
            (.ifte
              (.inOp false (.name "key") (.name "self"))
              (.seq
                (.assign "value" (.index (.name "self") (.name "key")))
                (.delIndex (.name "self") (.name "key")))
              (.ifte
                (.isOp false (.name "default") (.field (.name "self") "_Cache__marker"))
                (.raise (.unop "py:exception:KeyError" (.tupleE [(.name "key")])))
                (.assign "value" (.name "default"))))
            (.seq .skip (.seq (.ret (.name "value")) .skip))) }

/-- `cachetools/__init__.py:<module>.Cache.setdefault`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache_setdefault : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.setdefault"
  , params := ["key", "default"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true, defaults := [("default", (.lit .unit))] }
  , body := (.seq
            (.ifte
              (.inOp false (.name "key") (.name "self"))
              (.assign "value" (.index (.name "self") (.name "key")))
              (.seq
                (.assign "tmp0" (.name "default"))
                (.seq
                  (.setIndex (.name "self") (.name "key") (.name "tmp0"))
                  (.assign "value" (.name "tmp0")))))
            (.seq .skip (.seq (.ret (.name "value")) .skip))) }

/-- `cachetools/__init__.py:<module>.Cache.clear`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache_clear : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.clear"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.seq
              (.assign "tmp0" (.field (.name "self") "_Cache__data"))
              (.expr (.mcall (.name "tmp0") "clear" [])))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp1" (.field (.name "self") "_Cache__size"))
                  (.expr (.mcall (.name "tmp1") "clear" [])))
                (.seq .skip (.setField (.name "self") "_Cache__currsize" (.lit (.int 0))))))) }

/-- `cachetools/__init__.py:<module>.Cache.maxsize`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache_maxsize : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.maxsize"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.expr (.lit (.str "The maximum size of the cache.")))
            (.ret (.field (.name "self") "_Cache__maxsize"))) }

/-- `cachetools/__init__.py:<module>.Cache.currsize`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache_currsize : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.currsize"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.expr (.lit (.str "The current size of the cache.")))
            (.ret (.field (.name "self") "_Cache__currsize"))) }

/-- `cachetools/__init__.py:<module>.Cache.getsizeof`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache_getsizeof : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.getsizeof"
  , params := ["value"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["value"], isMethod := some false }
  , body := (.seq
            (.expr (.lit (.str "Return the size of a cache element's value.")))
            (.ret (.lit (.int 1)))) }

/-- `cachetools/__init__.py:<module>.FIFOCache.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__FIFOCache___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.FIFOCache.__init__"
  , params := ["maxsize", "getsizeof"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["maxsize"], isMethod := some true, defaults := [("getsizeof", (.lit .unit))] }
  , body := (.seq
            (.expr
              (.mcall
                (.field (.name "<module>cachetools/__init__.py") "Cache")
                "__init__"
                [(.name "self"), (.name "maxsize"), (.name "getsizeof")]))
            (.seq
              (.setField
                (.name "self")
                "_FIFOCache__order"
                (.hole "class-construction:unresolved-lexical-identity:OrderedDict"))
              (.seq .skip .skip))) }

/-- `cachetools/__init__.py:<module>.FIFOCache.__setitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__FIFOCache___setitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.FIFOCache.__setitem__"
  , params := ["key", "value", "cache_setitem"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key", "value"], isMethod := some true, defaults := [("cache_setitem", (.fnref "cachetools/__init__.py:<module>.Cache.__setitem__"))] }
  , body := (.seq
            (.expr
              (.callValue (.name "cache_setitem") [(.name "self"), (.name "key"), (.name "value")]))
            (.seq
              .skip
              (.ifte
                (.inOp false (.name "key") (.field (.name "self") "_FIFOCache__order"))
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_FIFOCache__order"))
                  (.expr (.mcall (.name "tmp0") "move_to_end" [(.name "key")])))
                (.setIndex (.field (.name "self") "_FIFOCache__order") (.name "key") (.lit .unit))))) }

/-- `cachetools/__init__.py:<module>.FIFOCache.__delitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__FIFOCache___delitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.FIFOCache.__delitem__"
  , params := ["key", "cache_delitem"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true, defaults := [("cache_delitem", (.fnref "cachetools/__init__.py:<module>.Cache.__delitem__"))] }
  , body := (.seq
            (.expr (.callValue (.name "cache_delitem") [(.name "self"), (.name "key")]))
            (.delIndex (.field (.name "self") "_FIFOCache__order") (.name "key"))) }

/-- `cachetools/__init__.py:<module>.FIFOCache.popitem`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__FIFOCache_popitem : Func :=
  { name := "cachetools/__init__.py:<module>.FIFOCache.popitem"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.expr (.lit (.str "Remove and return the `(key, value)` pair first inserted.")))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "$exprV$170" (.lit (.bool true)))
                  (.seq
                    (.tryCatch
                      (.assign
                        "key"
                        (.call
                          "next"
                          [(.call "iter" [(.field (.name "self") "_FIFOCache__order")])]))
                      "$exprV$169"
                      (.seq
                        (.assign "$exprV$170" (.lit (.bool false)))
                        (.ifte
                          (.inOp
                            false
                            (.name "$exprV$169")
                            (.tupleE [(.lit (.str "StopIteration"))]))
                          (.raise
                            (.unop
                              "py:exception:KeyError"
                              (.tupleE
                                [ (.binop
                                    "%"
                                    (.lit (.str "%s is empty"))
                                    (.field (.call "type" [(.name "self")]) "__name__")) ])))
                          (.raise (.name "$exprV$169")))))
                    (.ifte
                      (.name "$exprV$170")
                      (.ret
                        (.tupleE [(.name "key"), (.mcall (.name "self") "pop" [(.name "key")])]))
                      .skip)))
                (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/__init__.py:<module>.FIFOCache.clear`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__FIFOCache_clear : Func :=
  { name := "cachetools/__init__.py:<module>.FIFOCache.clear"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.expr
              (.mcall
                (.field (.name "<module>cachetools/__init__.py") "Cache")
                "clear"
                [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_FIFOCache__order"))
                  (.expr (.mcall (.name "tmp0") "clear" [])))
                .skip))) }

/-- `cachetools/__init__.py:<module>.LFUCache._Link.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LFUCache__Link___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.LFUCache._Link.__init__"
  , params := ["count"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["count"], isMethod := some true }
  , body := (.seq
            (.setField (.name "self") "count" (.name "count"))
            (.seq (.setField (.name "self") "keys" (.call "set" [])) .skip)) }

/-- `cachetools/__init__.py:<module>.LFUCache._Link.unlink`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LFUCache__Link_unlink : Func :=
  { name := "cachetools/__init__.py:<module>.LFUCache._Link.unlink"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.assign "next" (.field (.name "self") "next"))
            (.seq
              (.assign "prev" (.field (.name "self") "prev"))
              (.seq
                (.setField (.name "prev") "next" (.name "next"))
                (.seq .skip (.seq (.setField (.name "next") "prev" (.name "prev")) .skip))))) }

/-- `cachetools/__init__.py:<module>.LFUCache.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LFUCache___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.LFUCache.__init__"
  , params := ["maxsize", "getsizeof"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["maxsize"], isMethod := some true, defaults := [("getsizeof", (.lit .unit))] }
  , body := (.seq
            (.expr
              (.mcall
                (.field (.name "<module>cachetools/__init__.py") "Cache")
                "__init__"
                [(.name "self"), (.name "maxsize"), (.name "getsizeof")]))
            (.seq
              (.seq
                (.assign
                  "tmp0"
                  (.mcall
                    (.field (.name "<module>cachetools/__init__.py") "LFUCache")
                    "_Link"
                    [(.lit (.int 0))]))
                (.seq
                  (.setField (.name "self") "_LFUCache__root" (.name "tmp0"))
                  (.assign "root" (.name "tmp0"))))
              (.seq
                (.seq
                  (.assign "tmp1" (.name "root"))
                  (.seq
                    (.setField (.name "root") "prev" (.name "tmp1"))
                    (.setField (.name "root") "next" (.name "tmp1"))))
                (.seq
                  .skip
                  (.seq
                    (.seq
                      (.assign "tmp2" (.dictE []))
                      (.setField (.name "self") "_LFUCache__links" (.name "tmp2")))
                    (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))) }

/-- `cachetools/__init__.py:<module>.LFUCache.__getitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LFUCache___getitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.LFUCache.__getitem__"
  , params := ["key", "cache_getitem"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true, defaults := [("cache_getitem", (.fnref "cachetools/__init__.py:<module>.Cache.__getitem__"))] }
  , body := (.seq
            (.assign "value" (.callValue (.name "cache_getitem") [(.name "self"), (.name "key")]))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.inOp false (.name "key") (.name "self"))
                  (.expr (.mcall (.name "self") "_LFUCache__touch" [(.name "key")]))
                  .skip)
                (.ret (.name "value"))))) }

/-- `cachetools/__init__.py:<module>.LFUCache.__setitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LFUCache___setitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.LFUCache.__setitem__"
  , params := ["key", "value", "cache_setitem"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key", "value"], isMethod := some true, defaults := [("cache_setitem", (.fnref "cachetools/__init__.py:<module>.Cache.__setitem__"))] }
  , body := (.seq
            (.expr
              (.callValue (.name "cache_setitem") [(.name "self"), (.name "key"), (.name "value")]))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.inOp false (.name "key") (.field (.name "self") "_LFUCache__links"))
                  (.seq
                    (.expr (.mcall (.name "self") "_LFUCache__touch" [(.name "key")]))
                    (.ret (.lit .unit)))
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign "root" (.field (.name "self") "_LFUCache__root"))
                    (.seq
                      .skip
                      (.seq
                        (.assign "link" (.field (.name "root") "next"))
                        (.seq
                          .skip
                          (.seq
                            (.ifte
                              (.binop "!=" (.field (.name "link") "count") (.lit (.int 1)))
                              (.seq
                                (.assign
                                  "link"
                                  (.mcall
                                    (.field (.name "<module>cachetools/__init__.py") "LFUCache")
                                    "_Link"
                                    [(.lit (.int 1))]))
                                (.seq
                                  (.setField (.name "link") "next" (.field (.name "root") "next"))
                                  (.seq
                                    (.seq
                                      (.assign "tmp0" (.name "link"))
                                      (.seq
                                        (.setField (.name "root") "next" (.name "tmp0"))
                                        (.setField
                                        (.field (.name "link") "next")
                                        "prev"
                                        (.name "tmp0"))))
                                    (.setField (.name "link") "prev" (.name "root")))))
                              .skip)
                            (.seq
                              .skip
                              (.seq
                                (.seq
                                  (.assign "tmp1" (.field (.name "link") "keys"))
                                  (.expr (.mcall (.name "tmp1") "add" [(.name "key")])))
                                (.setIndex
                                  (.field (.name "self") "_LFUCache__links")
                                  (.name "key")
                                  (.name "link"))))))))))))) }

/-- `cachetools/__init__.py:<module>.LFUCache.__delitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LFUCache___delitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.LFUCache.__delitem__"
  , params := ["key", "cache_delitem"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true, defaults := [("cache_delitem", (.fnref "cachetools/__init__.py:<module>.Cache.__delitem__"))] }
  , body := (.seq
            (.expr (.callValue (.name "cache_delitem") [(.name "self"), (.name "key")]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_LFUCache__links"))
                  (.assign "link" (.mcall (.name "tmp0") "pop" [(.name "key")])))
                (.seq
                  .skip
                  (.seq
                    (.seq
                      (.assign "tmp1" (.field (.name "link") "keys"))
                      (.expr (.mcall (.name "tmp1") "remove" [(.name "key")])))
                    (.seq
                      .skip
                      (.ifte
                        (.unop "!" (.field (.name "link") "keys"))
                        (.expr (.mcall (.name "link") "unlink" []))
                        .skip))))))) }

/-- `cachetools/__init__.py:<module>.LFUCache.popitem`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LFUCache_popitem : Func :=
  { name := "cachetools/__init__.py:<module>.LFUCache.popitem"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.expr (.lit (.str "Remove and return the `(key, value)` pair least frequently used.")))
            (.seq
              .skip
              (.seq
                (.assign "root" (.field (.name "self") "_LFUCache__root"))
                (.seq
                  .skip
                  (.seq
                    (.assign "curr" (.field (.name "root") "next"))
                    (.seq
                      .skip
                      (.seq
                        (.ifte
                          (.isOp false (.name "curr") (.name "root"))
                          (.raise
                            (.unop
                              "py:exception:KeyError"
                              (.tupleE
                                [ (.binop
                                    "%"
                                    (.lit (.str "%s is empty"))
                                    (.field (.call "type" [(.name "self")]) "__name__")) ])))
                          .skip)
                        (.seq
                          .skip
                          (.seq
                            (.assign
                              "key"
                              (.call "next" [(.call "iter" [(.field (.name "curr") "keys")])]))
                            (.seq
                              .skip
                              (.seq
                                (.ret
                                  (.tupleE
                                    [(.name "key"), (.mcall (.name "self") "pop" [(.name "key")])]))
                                (.seq .skip .skip)))))))))))) }

/-- `cachetools/__init__.py:<module>.LFUCache.clear`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LFUCache_clear : Func :=
  { name := "cachetools/__init__.py:<module>.LFUCache.clear"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.expr
              (.mcall
                (.field (.name "<module>cachetools/__init__.py") "Cache")
                "clear"
                [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.assign "root" (.field (.name "self") "_LFUCache__root"))
                (.seq
                  .skip
                  (.seq
                    (.seq
                      (.assign "tmp0" (.name "root"))
                      (.seq
                        (.setField (.name "root") "prev" (.name "tmp0"))
                        (.setField (.name "root") "next" (.name "tmp0"))))
                    (.seq
                      .skip
                      (.seq
                        (.seq
                          (.assign "tmp1" (.field (.name "self") "_LFUCache__links"))
                          (.expr (.mcall (.name "tmp1") "clear" [])))
                        .skip))))))) }

/-- `cachetools/__init__.py:<module>.LFUCache._LFUCache__touch`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LFUCache__LFUCache__touch : Func :=
  { name := "cachetools/__init__.py:<module>.LFUCache._LFUCache__touch"
  , params := ["key"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true }
  , body := (.seq
            (.expr (.lit (.str "Increment use count")))
            (.seq
              .skip
              (.seq
                (.assign "link" (.index (.field (.name "self") "_LFUCache__links") (.name "key")))
                (.seq
                  .skip
                  (.seq
                    (.assign "curr" (.field (.name "link") "next"))
                    (.seq
                      .skip
                      (.seq
                        (.ifte
                          (.binop
                            "!="
                            (.field (.name "curr") "count")
                            (.binop "+" (.field (.name "link") "count") (.lit (.int 1))))
                          (.seq
                            (.ifte
                              (.binop
                                "=="
                                (.call "len" [(.field (.name "link") "keys")])
                                (.lit (.int 1)))
                              (.seq
                                (.setField
                                  (.name "link")
                                  "count"
                                  (.binop "+" (.field (.name "link") "count") (.lit (.int 1))))
                                (.ret (.lit .unit)))
                              .skip)
                            (.seq
                              (.assign
                                "curr"
                                (.mcall
                                  (.field (.name "<module>cachetools/__init__.py") "LFUCache")
                                  "_Link"
                                  [(.binop "+" (.field (.name "link") "count") (.lit (.int 1)))]))
                              (.seq
                                (.setField (.name "curr") "next" (.field (.name "link") "next"))
                                (.seq
                                  (.seq
                                    (.assign "tmp0" (.name "curr"))
                                    (.seq
                                      (.setField (.name "link") "next" (.name "tmp0"))
                                      (.setField
                                        (.field (.name "curr") "next")
                                        "prev"
                                        (.name "tmp0"))))
                                  (.setField (.name "curr") "prev" (.name "link"))))))
                          .skip)
                        (.seq
                          .skip
                          (.seq
                            (.seq
                              (.assign "tmp1" (.field (.name "curr") "keys"))
                              (.expr (.mcall (.name "tmp1") "add" [(.name "key")])))
                            (.seq
                              .skip
                              (.seq
                                (.seq
                                  (.assign "tmp2" (.field (.name "link") "keys"))
                                  (.expr (.mcall (.name "tmp2") "remove" [(.name "key")])))
                                (.seq
                                  .skip
                                  (.seq
                                    (.ifte
                                      (.unop "!" (.field (.name "link") "keys"))
                                      (.expr (.mcall (.name "link") "unlink" []))
                                      .skip)
                                    (.seq
                                      .skip
                                      (.setIndex
                                        (.field (.name "self") "_LFUCache__links")
                                        (.name "key")
                                        (.name "curr")))))))))))))))) }

/-- `cachetools/__init__.py:<module>.LRUCache.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LRUCache___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.LRUCache.__init__"
  , params := ["maxsize", "getsizeof"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["maxsize"], isMethod := some true, defaults := [("getsizeof", (.lit .unit))] }
  , body := (.seq
            (.expr
              (.mcall
                (.field (.name "<module>cachetools/__init__.py") "Cache")
                "__init__"
                [(.name "self"), (.name "maxsize"), (.name "getsizeof")]))
            (.seq
              (.setField
                (.name "self")
                "_LRUCache__order"
                (.hole "class-construction:unresolved-lexical-identity:OrderedDict"))
              (.seq .skip .skip))) }

/-- `cachetools/__init__.py:<module>.LRUCache.__getitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LRUCache___getitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.LRUCache.__getitem__"
  , params := ["key", "cache_getitem"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true, defaults := [("cache_getitem", (.fnref "cachetools/__init__.py:<module>.Cache.__getitem__"))] }
  , body := (.seq
            (.assign "value" (.callValue (.name "cache_getitem") [(.name "self"), (.name "key")]))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.inOp false (.name "key") (.name "self"))
                  (.expr (.mcall (.name "self") "_LRUCache__touch" [(.name "key")]))
                  .skip)
                (.ret (.name "value"))))) }

/-- `cachetools/__init__.py:<module>.LRUCache.__setitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LRUCache___setitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.LRUCache.__setitem__"
  , params := ["key", "value", "cache_setitem"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key", "value"], isMethod := some true, defaults := [("cache_setitem", (.fnref "cachetools/__init__.py:<module>.Cache.__setitem__"))] }
  , body := (.seq
            (.expr
              (.callValue (.name "cache_setitem") [(.name "self"), (.name "key"), (.name "value")]))
            (.expr (.mcall (.name "self") "_LRUCache__touch" [(.name "key")]))) }

/-- `cachetools/__init__.py:<module>.LRUCache.__delitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LRUCache___delitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.LRUCache.__delitem__"
  , params := ["key", "cache_delitem"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true, defaults := [("cache_delitem", (.fnref "cachetools/__init__.py:<module>.Cache.__delitem__"))] }
  , body := (.seq
            (.expr (.callValue (.name "cache_delitem") [(.name "self"), (.name "key")]))
            (.delIndex (.field (.name "self") "_LRUCache__order") (.name "key"))) }

/-- `cachetools/__init__.py:<module>.LRUCache.popitem`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LRUCache_popitem : Func :=
  { name := "cachetools/__init__.py:<module>.LRUCache.popitem"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.expr (.lit (.str "Remove and return the `(key, value)` pair least recently used.")))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "$exprV$172" (.lit (.bool true)))
                  (.seq
                    (.tryCatch
                      (.assign
                        "key"
                        (.call "next" [(.call "iter" [(.field (.name "self") "_LRUCache__order")])]))
                      "$exprV$171"
                      (.seq
                        (.assign "$exprV$172" (.lit (.bool false)))
                        (.ifte
                          (.inOp
                            false
                            (.name "$exprV$171")
                            (.tupleE [(.lit (.str "StopIteration"))]))
                          (.raise
                            (.unop
                              "py:exception:KeyError"
                              (.tupleE
                                [ (.binop
                                    "%"
                                    (.lit (.str "%s is empty"))
                                    (.field (.call "type" [(.name "self")]) "__name__")) ])))
                          (.raise (.name "$exprV$171")))))
                    (.ifte
                      (.name "$exprV$172")
                      (.ret
                        (.tupleE [(.name "key"), (.mcall (.name "self") "pop" [(.name "key")])]))
                      .skip)))
                (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/__init__.py:<module>.LRUCache.clear`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LRUCache_clear : Func :=
  { name := "cachetools/__init__.py:<module>.LRUCache.clear"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.expr
              (.mcall
                (.field (.name "<module>cachetools/__init__.py") "Cache")
                "clear"
                [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_LRUCache__order"))
                  (.expr (.mcall (.name "tmp0") "clear" [])))
                .skip))) }

/-- `cachetools/__init__.py:<module>.LRUCache._LRUCache__touch`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LRUCache__LRUCache__touch : Func :=
  { name := "cachetools/__init__.py:<module>.LRUCache._LRUCache__touch"
  , params := ["key"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true }
  , body := (.seq
            (.expr (.lit (.str "Mark as recently used")))
            (.seq
              .skip
              (.tryCatch
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_LRUCache__order"))
                  (.expr (.mcall (.name "tmp0") "move_to_end" [(.name "key")])))
                "$exprV$173"
                (.ifte
                  (.inOp false (.name "$exprV$173") (.tupleE [(.lit (.str "KeyError"))]))
                  (.setIndex (.field (.name "self") "_LRUCache__order") (.name "key") (.lit .unit))
                  (.raise (.name "$exprV$173")))))) }

/-- `cachetools/__init__.py:<module>.RRCache.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__RRCache___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.RRCache.__init__"
  , params := ["maxsize", "choice", "getsizeof"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["maxsize"], isMethod := some true, defaults := [("choice", (.fnref "cachetools/__init__.py:<module>.RRCache.choice")), ("getsizeof", (.lit .unit))] }
  , body := (.seq
            (.expr
              (.mcall
                (.field (.name "<module>cachetools/__init__.py") "Cache")
                "__init__"
                [(.name "self"), (.name "maxsize"), (.name "getsizeof")]))
            (.seq
              (.setField (.name "self") "_RRCache__choice" (.name "choice"))
              (.seq
                (.seq
                  (.assign "tmp0" (.dictE []))
                  (.setField (.name "self") "_RRCache__index" (.name "tmp0")))
                (.seq (.setField (.name "self") "_RRCache__keys" (.listE [])) (.seq .skip .skip))))) }

/-- `cachetools/__init__.py:<module>.RRCache.choice`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__RRCache_choice : Func :=
  { name := "cachetools/__init__.py:<module>.RRCache.choice"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.expr (.lit (.str "The `choice` function used by the cache.")))
            (.ret (.field (.name "self") "_RRCache__choice"))) }

/-- `cachetools/__init__.py:<module>.RRCache.__setitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__RRCache___setitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.RRCache.__setitem__"
  , params := ["key", "value", "cache_setitem"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key", "value"], isMethod := some true, defaults := [("cache_setitem", (.fnref "cachetools/__init__.py:<module>.Cache.__setitem__"))] }
  , body := (.seq
            (.expr
              (.callValue (.name "cache_setitem") [(.name "self"), (.name "key"), (.name "value")]))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.inOp true (.name "key") (.field (.name "self") "_RRCache__index"))
                  (.seq
                    (.setIndex
                      (.field (.name "self") "_RRCache__index")
                      (.name "key")
                      (.call "len" [(.field (.name "self") "_RRCache__keys")]))
                    (.seq
                      (.assign "tmp0" (.field (.name "self") "_RRCache__keys"))
                      (.expr (.mcall (.name "tmp0") "append" [(.name "key")]))))
                  .skip)
                .skip))) }

/-- `cachetools/__init__.py:<module>.RRCache.__delitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__RRCache___delitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.RRCache.__delitem__"
  , params := ["key", "cache_delitem"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true, defaults := [("cache_delitem", (.fnref "cachetools/__init__.py:<module>.Cache.__delitem__"))] }
  , body := (.seq
            (.expr (.callValue (.name "cache_delitem") [(.name "self"), (.name "key")]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_RRCache__index"))
                  (.assign "index" (.mcall (.name "tmp0") "pop" [(.name "key")])))
                (.seq
                  .skip
                  (.seq
                    (.ifte
                      (.binop
                        "!="
                        (.name "index")
                        (.binop
                          "-"
                          (.call "len" [(.field (.name "self") "_RRCache__keys")])
                          (.lit (.int 1))))
                      (.seq
                        (.assign
                          "last"
                          (.index
                            (.field (.name "self") "_RRCache__keys")
                            (.unop "-" (.lit (.int 1)))))
                        (.seq
                          (.setIndex
                            (.field (.name "self") "_RRCache__keys")
                            (.name "index")
                            (.name "last"))
                          (.setIndex
                            (.field (.name "self") "_RRCache__index")
                            (.name "last")
                            (.name "index"))))
                      .skip)
                    (.seq
                      .skip
                      (.seq
                        (.seq
                          (.assign "tmp1" (.field (.name "self") "_RRCache__keys"))
                          (.expr (.mcall (.name "tmp1") "pop" [])))
                        (.seq .skip .skip)))))))) }

/-- `cachetools/__init__.py:<module>.RRCache.popitem`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__RRCache_popitem : Func :=
  { name := "cachetools/__init__.py:<module>.RRCache.popitem"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.expr (.lit (.str "Remove and return a random `(key, value)` pair.")))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "$exprV$175" (.lit (.bool true)))
                  (.seq
                    (.tryCatch
                      (.assign
                        "key"
                        (.mcall
                          (.name "self")
                          "_RRCache__choice"
                          [(.field (.name "self") "_RRCache__keys")]))
                      "$exprV$174"
                      (.seq
                        (.assign "$exprV$175" (.lit (.bool false)))
                        (.ifte
                          (.inOp false (.name "$exprV$174") (.tupleE [(.lit (.str "IndexError"))]))
                          (.raise
                            (.unop
                              "py:exception:KeyError"
                              (.tupleE
                                [ (.binop
                                    "%"
                                    (.lit (.str "%s is empty"))
                                    (.field (.call "type" [(.name "self")]) "__name__")) ])))
                          (.raise (.name "$exprV$174")))))
                    (.ifte
                      (.name "$exprV$175")
                      (.ret
                        (.tupleE [(.name "key"), (.mcall (.name "self") "pop" [(.name "key")])]))
                      .skip)))
                (.seq .skip .skip)))) }

/-- `cachetools/__init__.py:<module>.RRCache.clear`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__RRCache_clear : Func :=
  { name := "cachetools/__init__.py:<module>.RRCache.clear"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.expr
              (.mcall
                (.field (.name "<module>cachetools/__init__.py") "Cache")
                "clear"
                [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_RRCache__index"))
                  (.expr (.mcall (.name "tmp0") "clear" [])))
                (.seq
                  .skip
                  (.delSlice
                    (.field (.name "self") "_RRCache__keys")
                    (.lit .unit)
                    (.lit .unit)
                    (.lit .unit)))))) }

/-- `cachetools/__init__.py:<module>._TimedCache._Timer.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache__Timer___init__ : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache._Timer.__init__"
  , params := ["timer"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["timer"], isMethod := some true }
  , body := (.seq
            (.setField (.name "self") "_Timer__timer" (.name "timer"))
            (.setField (.name "self") "_Timer__nesting" (.lit (.int 0)))) }

/-- `cachetools/__init__.py:<module>._TimedCache._Timer.__call__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache__Timer___call__ : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache._Timer.__call__"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.ifte
            (.binop "==" (.field (.name "self") "_Timer__nesting") (.lit (.int 0)))
            (.ret (.mcall (.name "self") "_Timer__timer" []))
            (.ret (.field (.name "self") "_Timer__time"))) }

/-- `cachetools/__init__.py:<module>._TimedCache._Timer.__enter__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache__Timer___enter__ : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache._Timer.__enter__"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.ifte
              (.binop "==" (.field (.name "self") "_Timer__nesting") (.lit (.int 0)))
              (.seq
                (.assign "tmp0" (.mcall (.name "self") "_Timer__timer" []))
                (.seq
                  (.setField (.name "self") "_Timer__time" (.name "tmp0"))
                  (.assign "time" (.name "tmp0"))))
              (.assign "time" (.field (.name "self") "_Timer__time")))
            (.seq
              .skip
              (.seq
                (.setField
                  (.name "self")
                  "_Timer__nesting"
                  (.binop "+" (.field (.name "self") "_Timer__nesting") (.lit (.int 1))))
                (.seq .skip (.ret (.name "time")))))) }

/-- `cachetools/__init__.py:<module>._TimedCache._Timer.__exit__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache__Timer___exit__ : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache._Timer.__exit__"
  , params := ["exc"]
  , vararg := some "exc"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.setField
            (.name "self")
            "_Timer__nesting"
            (.binop "-" (.field (.name "self") "_Timer__nesting") (.lit (.int 1)))) }

/-- `cachetools/__init__.py:<module>._TimedCache._Timer.__reduce__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache__Timer___reduce__ : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache._Timer.__reduce__"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.ret
              (.tupleE
                [ (.field (.field (.name "<module>cachetools/__init__.py") "_TimedCache") "_Timer")
                , (.tupleE [(.field (.name "self") "_Timer__timer")]) ]))
            .skip) }

/-- `cachetools/__init__.py:<module>._TimedCache._Timer.__getattr__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache__Timer___getattr__ : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache._Timer.__getattr__"
  , params := ["name"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["name"], isMethod := some true }
  , body := (.seq
            (.ret (.call "getattr" [(.field (.name "self") "_Timer__timer"), (.name "name")]))
            .skip) }

/-- `cachetools/__init__.py:<module>._TimedCache.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache___init__ : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.__init__"
  , params := ["maxsize", "timer", "getsizeof"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["maxsize", "timer"], isMethod := some true, defaults := [("getsizeof", (.lit .unit))] }
  , body := (.seq
            (.expr
              (.mcall
                (.field (.name "<module>cachetools/__init__.py") "Cache")
                "__init__"
                [(.name "self"), (.name "maxsize"), (.name "getsizeof")]))
            (.seq
              (.setField
                (.name "self")
                "_TimedCache__timer"
                (.mcall
                  (.field (.name "<module>cachetools/__init__.py") "_TimedCache")
                  "_Timer"
                  [(.name "timer")]))
              (.seq .skip .skip))) }

/-- `cachetools/__init__.py:<module>._TimedCache.__repr__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache___repr__ : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.__repr__"
  , params := ["cache_repr"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, defaults := [("cache_repr", (.fnref "cachetools/__init__.py:<module>.Cache.__repr__"))] }
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "_TimedCache__timer"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.seq
                        (.assign "time" (.name "value_tmp0"))
                        (.seq
                          (.expr (.mcall (.name "self") "expire" [(.name "time")]))
                          (.ret (.callValue (.name "cache_repr") [(.name "self")]))))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/__init__.py:<module>._TimedCache.__len__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache___len__ : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.__len__"
  , params := ["cache_len"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, defaults := [("cache_len", (.fnref "cachetools/__init__.py:<module>.Cache.__len__"))] }
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "_TimedCache__timer"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.seq
                        (.assign "time" (.name "value_tmp0"))
                        (.seq
                          (.expr (.mcall (.name "self") "expire" [(.name "time")]))
                          (.ret (.callValue (.name "cache_len") [(.name "self")]))))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/__init__.py:<module>._TimedCache.currsize`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache_currsize : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.currsize"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "_TimedCache__timer"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.seq
                        (.assign "time" (.name "value_tmp0"))
                        (.seq
                          (.expr (.mcall (.name "self") "expire" [(.name "time")]))
                          (.ret (.field (.call "super" []) "currsize"))))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))) }

/-- `cachetools/__init__.py:<module>._TimedCache.timer`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache_timer : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.timer"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.expr (.lit (.str "The timer function used by the cache.")))
            (.ret (.field (.name "self") "_TimedCache__timer"))) }

/-- `cachetools/__init__.py:<module>._TimedCache.get`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache_get : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.get"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, receiverName := some "self" }
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "_TimedCache__timer"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.ret
                        (.mcall
                          (.field (.name "<module>cachetools/__init__.py") "Cache")
                          "get"
                          [(.name "self"), (.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/__init__.py:<module>._TimedCache.pop`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache_pop : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.pop"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, receiverName := some "self" }
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "_TimedCache__timer"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.ret
                        (.mcall
                          (.field (.name "<module>cachetools/__init__.py") "Cache")
                          "pop"
                          [(.name "self"), (.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/__init__.py:<module>._TimedCache.setdefault`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache_setdefault : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.setdefault"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, receiverName := some "self" }
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "_TimedCache__timer"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.ret
                        (.mcall
                          (.field (.name "<module>cachetools/__init__.py") "Cache")
                          "setdefault"
                          [(.name "self"), (.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/__init__.py:<module>._TimedCache.clear`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache_clear : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.clear"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.expr
              (.mcall
                (.field (.name "<module>cachetools/__init__.py") "Cache")
                "clear"
                [(.name "self")]))
            .skip) }

/-- `cachetools/__init__.py:<module>._TimedCache.expire`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache_expire : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.expire"
  , params := ["time"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, defaults := [("time", (.lit .unit))] }
  , body := (.seq (.raise (.unop "py:exception:NotImplementedError" (.tupleE []))) .skip) }

/-- `cachetools/__init__.py:<module>.TTLCache._Link.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache__Link___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache._Link.__init__"
  , params := ["key", "expires"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, defaults := [("key", (.lit .unit)), ("expires", (.lit .unit))] }
  , body := (.seq
            (.setField (.name "self") "key" (.name "key"))
            (.setField (.name "self") "expires" (.name "expires"))) }

/-- `cachetools/__init__.py:<module>.TTLCache._Link.__reduce__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache__Link___reduce__ : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache._Link.__reduce__"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.ret
              (.tupleE
                [ (.field (.field (.name "<module>cachetools/__init__.py") "TTLCache") "_Link")
                , (.tupleE [(.field (.name "self") "key"), (.field (.name "self") "expires")]) ]))
            .skip) }

/-- `cachetools/__init__.py:<module>.TTLCache._Link.unlink`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache__Link_unlink : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache._Link.unlink"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.assign "next" (.field (.name "self") "next"))
            (.seq
              (.assign "prev" (.field (.name "self") "prev"))
              (.seq
                (.setField (.name "prev") "next" (.name "next"))
                (.seq .skip (.seq (.setField (.name "next") "prev" (.name "prev")) .skip))))) }

/-- `cachetools/__init__.py:<module>.TTLCache.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.__init__"
  , params := ["maxsize", "ttl", "timer", "getsizeof"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["maxsize", "ttl"], isMethod := some true, defaults := [("timer", (.fnref "<absent:external>time.monotonic")), ("getsizeof", (.lit .unit))] }
  , body := (.seq
            (.expr
              (.mcall
                (.field (.name "<module>cachetools/__init__.py") "_TimedCache")
                "__init__"
                [(.name "self"), (.name "maxsize"), (.name "timer"), (.name "getsizeof")]))
            (.seq
              (.seq
                (.assign
                  "tmp0"
                  (.mcall (.field (.name "<module>cachetools/__init__.py") "TTLCache") "_Link" []))
                (.seq
                  (.setField (.name "self") "_TTLCache__root" (.name "tmp0"))
                  (.assign "root" (.name "tmp0"))))
              (.seq
                (.seq
                  (.assign "tmp1" (.name "root"))
                  (.seq
                    (.setField (.name "root") "prev" (.name "tmp1"))
                    (.setField (.name "root") "next" (.name "tmp1"))))
                (.seq
                  (.setField
                    (.name "self")
                    "_TTLCache__links"
                    (.hole "class-construction:unresolved-lexical-identity:OrderedDict"))
                  (.seq
                    .skip
                    (.seq
                      (.setField (.name "self") "_TTLCache__ttl" (.name "ttl"))
                      (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))) }

/-- `cachetools/__init__.py:<module>.TTLCache.__contains__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache___contains__ : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.__contains__"
  , params := ["key"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true }
  , body := (.seq
            (.seq
              (.assign "$exprV$177" (.lit (.bool true)))
              (.seq
                (.tryCatch
                  (.assign "link" (.index (.field (.name "self") "_TTLCache__links") (.name "key")))
                  "$exprV$176"
                  (.seq
                    (.assign "$exprV$177" (.lit (.bool false)))
                    (.ifte
                      (.inOp false (.name "$exprV$176") (.tupleE [(.lit (.str "KeyError"))]))
                      (.ret (.lit (.bool false)))
                      (.raise (.name "$exprV$176")))))
                (.ifte
                  (.name "$exprV$177")
                  (.ret
                    (.binop
                      "<"
                      (.mcall (.name "self") "timer" [])
                      (.field (.name "link") "expires")))
                  .skip)))
            .skip) }

/-- `cachetools/__init__.py:<module>.TTLCache.__getitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache___getitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.__getitem__"
  , params := ["key", "cache_getitem"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true, defaults := [("cache_getitem", (.fnref "cachetools/__init__.py:<module>.Cache.__getitem__"))] }
  , body := (.seq
            (.seq
              (.assign "$exprV$179" (.lit (.bool true)))
              (.seq
                (.tryCatch
                  (.assign "link" (.mcall (.name "self") "_TTLCache__getlink" [(.name "key")]))
                  "$exprV$178"
                  (.seq
                    (.assign "$exprV$179" (.lit (.bool false)))
                    (.ifte
                      (.inOp false (.name "$exprV$178") (.tupleE [(.lit (.str "KeyError"))]))
                      (.assign "expired" (.lit (.bool false)))
                      (.raise (.name "$exprV$178")))))
                (.ifte
                  (.name "$exprV$179")
                  (.assign
                    "expired"
                    (.unop
                      "!"
                      (.binop
                        "<"
                        (.mcall (.name "self") "timer" [])
                        (.field (.name "link") "expires"))))
                  .skip)))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.name "expired")
                  (.ret (.mcall (.name "self") "__missing__" [(.name "key")]))
                  (.ret (.callValue (.name "cache_getitem") [(.name "self"), (.name "key")])))
                .skip))) }

/-- `cachetools/__init__.py:<module>.TTLCache.__setitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache___setitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.__setitem__"
  , params := ["key", "value", "cache_setitem"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key", "value"], isMethod := some true, defaults := [("cache_setitem", (.fnref "cachetools/__init__.py:<module>.Cache.__setitem__"))] }
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "timer"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.seq
                        (.assign "time" (.name "value_tmp0"))
                        (.seq
                          (.expr (.mcall (.name "self") "expire" [(.name "time")]))
                          (.expr
                            (.callValue
                              (.name "cache_setitem")
                              [(.name "self"), (.name "key"), (.name "value")]))))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq
              (.seq
                (.assign "$exprV$181" (.lit (.bool true)))
                (.seq
                  (.tryCatch
                    (.assign "link" (.mcall (.name "self") "_TTLCache__getlink" [(.name "key")]))
                    "$exprV$180"
                    (.seq
                      (.assign "$exprV$181" (.lit (.bool false)))
                      (.ifte
                        (.inOp false (.name "$exprV$180") (.tupleE [(.lit (.str "KeyError"))]))
                        (.seq
                          (.assign
                            "tmp0"
                            (.mcall
                              (.field (.name "<module>cachetools/__init__.py") "TTLCache")
                              "_Link"
                              [(.name "key")]))
                          (.seq
                            (.setIndex
                              (.field (.name "self") "_TTLCache__links")
                              (.name "key")
                              (.name "tmp0"))
                            (.assign "link" (.name "tmp0"))))
                        (.raise (.name "$exprV$180")))))
                  (.ifte (.name "$exprV$181") (.expr (.mcall (.name "link") "unlink" [])) .skip)))
              (.seq
                .skip
                (.seq
                  (.setField
                    (.name "link")
                    "expires"
                    (.binop "+" (.name "time") (.field (.name "self") "_TTLCache__ttl")))
                  (.seq
                    .skip
                    (.seq
                      (.seq
                        (.assign "tmp1" (.field (.name "self") "_TTLCache__root"))
                        (.seq
                          (.setField (.name "link") "next" (.name "tmp1"))
                          (.assign "root" (.name "tmp1"))))
                      (.seq
                        .skip
                        (.seq
                          (.seq
                            (.assign "tmp2" (.field (.name "root") "prev"))
                            (.seq
                              (.setField (.name "link") "prev" (.name "tmp2"))
                              (.assign "prev" (.name "tmp2"))))
                          (.seq
                            .skip
                            (.seq
                              (.seq
                                (.assign "tmp3" (.name "link"))
                                (.seq
                                  (.setField (.name "prev") "next" (.name "tmp3"))
                                  (.setField (.name "root") "prev" (.name "tmp3"))))
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))))))) }

/-- `cachetools/__init__.py:<module>.TTLCache.__delitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache___delitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.__delitem__"
  , params := ["key", "cache_delitem"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true, defaults := [("cache_delitem", (.fnref "cachetools/__init__.py:<module>.Cache.__delitem__"))] }
  , body := (.seq
            (.expr (.callValue (.name "cache_delitem") [(.name "self"), (.name "key")]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_TTLCache__links"))
                  (.assign "link" (.mcall (.name "tmp0") "pop" [(.name "key")])))
                (.seq
                  .skip
                  (.seq
                    (.expr (.mcall (.name "link") "unlink" []))
                    (.seq
                      .skip
                      (.ifte
                        (.unop
                          "!"
                          (.binop
                            "<"
                            (.mcall (.name "self") "timer" [])
                            (.field (.name "link") "expires")))
                        (.raise (.unop "py:exception:KeyError" (.tupleE [(.name "key")])))
                        .skip))))))) }

/-- `cachetools/__init__.py:<module>.TTLCache.__iter__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache___iter__ : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.__iter__"
  , params := []
  , analysisBody := some (.seq
            (.assign "root" (.field (.name "self") "_TTLCache__root"))
            (.seq
              .skip
              (.seq
                (.assign "curr" (.field (.name "root") "next"))
                (.seq
                  .skip
                  (.seq
                    (.loop
                      (.isOp true (.name "curr") (.name "root"))
                      (.seq
                        (.seq
                          (.assign "manager_tmp0" (.field (.name "self") "timer"))
                          (.seq
                            (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                            (.seq
                              (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                              (.seq
                                (.assign
                                  "value_tmp0"
                                  (.mcall (.name "manager_tmp0") "__enter__" []))
                                (.tryFinally
                                  (.seq
                                    (.assign "time" (.name "value_tmp0"))
                                    (.ifte
                                      (.binop "<" (.name "time") (.field (.name "curr") "expires"))
                                      (.expr (.field (.name "curr") "key"))
                                      .skip))
                                  (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                        (.assign "curr" (.field (.name "curr") "next"))))
                    (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.assign "<generator-frame>" (.alloc "<generator>" []))
            (.seq
              (.setField
                (.name "<generator-frame>")
                "<locals>"
                (.dictE [((.lit (.str "self")), (.name "self"))]))
              (.seq
                (.setField
                  (.name "<generator-frame>")
                  "<resume>"
                  (.fnref "<generator>.cachetools/__init__.py:<module>.TTLCache.__iter__.<resume>"))
                (.seq
                  (.setField (.name "<generator-frame>") "<pc>" (.lit (.int 19)))
                  (.seq
                    (.setField (.name "<generator-frame>") "<state>" (.lit (.int 0)))
                    (.seq
                      (.setField (.name "<generator-frame>") "<return>" (.lit .unit))
                      (.seq (.ret (.name "<generator-frame>")) .skip))))))) }

/-- `cachetools/__init__.py:<module>.TTLCache.__setstate__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache___setstate__ : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.__setstate__"
  , params := ["state"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["state"], isMethod := some true }
  , body := (.seq
            (.seq
              (.assign "tmp0" (.field (.name "self") "__dict__"))
              (.expr (.mcall (.name "tmp0") "update" [(.name "state")])))
            (.seq
              (.assign "root" (.field (.name "self") "_TTLCache__root"))
              (.seq
                (.seq
                  (.assign "tmp1" (.name "root"))
                  (.seq
                    (.setField (.name "root") "prev" (.name "tmp1"))
                    (.setField (.name "root") "next" (.name "tmp1"))))
                (.seq
                  (.seq
                    (.seq
                      (.assign "tmp6" (.field (.name "self") "_TTLCache__links"))
                      (.assign
                        "tmp5"
                        (.call
                          "sorted"
                          [ (.mcall (.name "tmp6") "values" [])
                          , (.kwargE
                              "key"
                              (.fnref
                                "cachetools/__init__.py:<module>.TTLCache.__setstate__.<lambda>0")) ])))
                    (.forIn
                      "link"
                      (.name "tmp5")
                      (.seq
                        (.setField (.name "link") "next" (.name "root"))
                        (.seq
                          (.seq
                            (.assign "tmp2" (.field (.name "root") "prev"))
                            (.seq
                              (.setField (.name "link") "prev" (.name "tmp2"))
                              (.assign "prev" (.name "tmp2"))))
                          (.seq
                            (.assign "tmp3" (.name "link"))
                            (.seq
                              (.setField (.name "prev") "next" (.name "tmp3"))
                              (.setField (.name "root") "prev" (.name "tmp3"))))))))
                  (.seq
                    .skip
                    (.seq
                      (.expr (.mcall (.name "self") "expire" [(.mcall (.name "self") "timer" [])]))
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))) }

/-- `cachetools/__init__.py:<module>.TTLCache.__setstate__.<lambda>0`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache___setstate____lambda_0 : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.__setstate__.<lambda>0"
  , params := ["obj"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["obj"], isMethod := some false }
  , body := (.ret (.field (.name "obj") "expires")) }

/-- `cachetools/__init__.py:<module>.TTLCache.ttl`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache_ttl : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.ttl"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.expr (.lit (.str "The time-to-live value of the cache's items.")))
            (.ret (.field (.name "self") "_TTLCache__ttl"))) }

/-- `cachetools/__init__.py:<module>.TTLCache.expire`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache_expire : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.expire"
  , params := ["time"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, defaults := [("time", (.lit .unit))] }
  , body := (.seq
            (.expr
              (.lit
                (.str "Remove expired items from the cache and return an iterable of the\n        expired `(key, value)` pairs.\n\n        ")))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.isOp false (.name "time") (.lit .unit))
                  (.assign "time" (.mcall (.name "self") "timer" []))
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign "root" (.field (.name "self") "_TTLCache__root"))
                    (.seq
                      .skip
                      (.seq
                        (.assign "curr" (.field (.name "root") "next"))
                        (.seq
                          .skip
                          (.seq
                            (.assign "links" (.field (.name "self") "_TTLCache__links"))
                            (.seq
                              .skip
                              (.seq
                                (.assign "expired" (.listE []))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign
                                      "cache_delitem"
                                      (.field
                                        (.field (.name "<module>cachetools/__init__.py") "Cache")
                                        "__delitem__"))
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign
                                        "cache_getitem"
                                        (.field
                                        (.field (.name "<module>cachetools/__init__.py") "Cache")
                                        "__getitem__"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.loop
                                        (.lit (.bool true))
                                        (.seq
                                        (.assign
                                        "$exprV$183"
                                        (.isOp true (.name "curr") (.name "root")))
                                        (.seq
                                        (.ifte
                                        (.name "$exprV$183")
                                        (.seq
                                        (.assign
                                        "$exprV$184"
                                        (.unop
                                        "!"
                                        (.binop
                                        "<"
                                        (.name "time")
                                        (.field (.name "curr") "expires"))))
                                        (.assign "$exprV$185" (.lit (.int 0))))
                                        (.seq
                                        (.assign "$exprV$184" (.name "$exprV$183"))
                                        (.assign "$exprV$185" (.lit (.int 1)))))
                                        (.ifte
                                        (.cond
                                        (.binop "==" (.name "$exprV$185") (.lit (.int 0)))
                                        (.cond
                                        (.name "$exprV$184")
                                        (.lit (.bool true))
                                        (.lit (.bool false)))
                                        (.binop "==" (.name "$exprV$185") (.lit (.int 2))))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.name "expired")
                                        "append"
                                        [ (.tupleE
                                        [ (.field (.name "curr") "key")
                                        , (.callValue
                                        (.name "cache_getitem")
                                        [(.name "self"), (.field (.name "curr") "key")]) ]) ]))
                                        (.seq
                                        (.expr
                                        (.callValue
                                        (.name "cache_delitem")
                                        [(.name "self"), (.field (.name "curr") "key")]))
                                        (.seq
                                        (.delIndex (.name "links") (.field (.name "curr") "key"))
                                        (.seq
                                        (.assign "next" (.field (.name "curr") "next"))
                                        (.seq
                                        (.expr (.mcall (.name "curr") "unlink" []))
                                        (.assign "curr" (.name "next")))))))
                                        .brk))))
                                        (.ret (.name "expired"))))))))))))))))))) }

/-- `cachetools/__init__.py:<module>.TTLCache.popitem`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache_popitem : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.popitem"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.expr
              (.lit
                (.str "Remove and return the `(key, value)` pair least recently used that\n        has not already expired.\n\n        ")))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "manager_tmp0" (.field (.name "self") "timer"))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.seq
                            (.assign "time" (.name "value_tmp0"))
                            (.seq
                              (.expr (.mcall (.name "self") "expire" [(.name "time")]))
                              (.seq
                                (.assign "$exprV$187" (.lit (.bool true)))
                                (.seq
                                  (.tryCatch
                                    (.assign
                                      "key"
                                      (.call
                                        "next"
                                        [ (.call "iter" [(.field (.name "self") "_TTLCache__links")]) ]))
                                    "$exprV$186"
                                    (.seq
                                      (.assign "$exprV$187" (.lit (.bool false)))
                                      (.ifte
                                        (.inOp
                                        false
                                        (.name "$exprV$186")
                                        (.tupleE [(.lit (.str "StopIteration"))]))
                                        (.raise
                                        (.unop
                                        "py:exception:KeyError"
                                        (.tupleE
                                        [ (.binop
                                        "%"
                                        (.lit (.str "%s is empty"))
                                        (.field (.call "type" [(.name "self")]) "__name__")) ])))
                                        (.raise (.name "$exprV$186")))))
                                  (.ifte
                                    (.name "$exprV$187")
                                    (.ret
                                      (.tupleE
                                        [ (.name "key")
                                        , (.mcall (.name "self") "pop" [(.name "key")]) ]))
                                    .skip)))))
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))) }

/-- `cachetools/__init__.py:<module>.TTLCache.clear`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache_clear : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.clear"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.expr
              (.mcall
                (.field (.name "<module>cachetools/__init__.py") "_TimedCache")
                "clear"
                [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.assign "root" (.field (.name "self") "_TTLCache__root"))
                (.seq
                  .skip
                  (.seq
                    (.seq
                      (.assign "tmp0" (.name "root"))
                      (.seq
                        (.setField (.name "root") "prev" (.name "tmp0"))
                        (.setField (.name "root") "next" (.name "tmp0"))))
                    (.seq
                      .skip
                      (.seq
                        (.seq
                          (.assign "tmp1" (.field (.name "self") "_TTLCache__links"))
                          (.expr (.mcall (.name "tmp1") "clear" [])))
                        .skip))))))) }

/-- `cachetools/__init__.py:<module>.TTLCache._TTLCache__getlink`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache__TTLCache__getlink : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache._TTLCache__getlink"
  , params := ["key"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true }
  , body := (.seq
            (.assign "value" (.index (.field (.name "self") "_TTLCache__links") (.name "key")))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_TTLCache__links"))
                  (.expr (.mcall (.name "tmp0") "move_to_end" [(.name "key")])))
                (.seq .skip (.ret (.name "value")))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache._Item.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache__Item___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache._Item.__init__"
  , params := ["key", "expires"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, defaults := [("key", (.lit .unit)), ("expires", (.lit .unit))] }
  , body := (.seq
            (.setField (.name "self") "key" (.name "key"))
            (.seq
              (.setField (.name "self") "expires" (.name "expires"))
              (.setField (.name "self") "removed" (.lit (.bool false))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache._Item.__lt__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache__Item___lt__ : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache._Item.__lt__"
  , params := ["other"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["other"], isMethod := some true }
  , body := (.ret (.binop "<" (.field (.name "self") "expires") (.field (.name "other") "expires"))) }

/-- `cachetools/__init__.py:<module>.TLRUCache.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.__init__"
  , params := ["maxsize", "ttu", "timer", "getsizeof"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["maxsize", "ttu"], isMethod := some true, defaults := [("timer", (.fnref "<absent:external>time.monotonic")), ("getsizeof", (.lit .unit))] }
  , body := (.seq
            (.expr
              (.mcall
                (.field (.name "<module>cachetools/__init__.py") "_TimedCache")
                "__init__"
                [(.name "self"), (.name "maxsize"), (.name "timer"), (.name "getsizeof")]))
            (.seq
              (.setField
                (.name "self")
                "_TLRUCache__items"
                (.hole "class-construction:unresolved-lexical-identity:OrderedDict"))
              (.seq
                (.setField (.name "self") "_TLRUCache__order" (.listE []))
                (.seq (.setField (.name "self") "_TLRUCache__ttu" (.name "ttu")) (.seq .skip .skip))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache.__contains__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache___contains__ : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.__contains__"
  , params := ["key"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true }
  , body := (.seq
            (.seq
              (.assign "$exprV$189" (.lit (.bool true)))
              (.seq
                (.tryCatch
                  (.assign
                    "item"
                    (.index (.field (.name "self") "_TLRUCache__items") (.name "key")))
                  "$exprV$188"
                  (.seq
                    (.assign "$exprV$189" (.lit (.bool false)))
                    (.ifte
                      (.inOp false (.name "$exprV$188") (.tupleE [(.lit (.str "KeyError"))]))
                      (.ret (.lit (.bool false)))
                      (.raise (.name "$exprV$188")))))
                (.ifte
                  (.name "$exprV$189")
                  (.ret
                    (.binop
                      "<"
                      (.mcall (.name "self") "timer" [])
                      (.field (.name "item") "expires")))
                  .skip)))
            .skip) }

/-- `cachetools/__init__.py:<module>.TLRUCache.__getitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache___getitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.__getitem__"
  , params := ["key", "cache_getitem"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true, defaults := [("cache_getitem", (.fnref "cachetools/__init__.py:<module>.Cache.__getitem__"))] }
  , body := (.seq
            (.seq
              (.assign "$exprV$191" (.lit (.bool true)))
              (.seq
                (.tryCatch
                  (.assign "item" (.mcall (.name "self") "_TLRUCache__getitem" [(.name "key")]))
                  "$exprV$190"
                  (.seq
                    (.assign "$exprV$191" (.lit (.bool false)))
                    (.ifte
                      (.inOp false (.name "$exprV$190") (.tupleE [(.lit (.str "KeyError"))]))
                      (.assign "expired" (.lit (.bool false)))
                      (.raise (.name "$exprV$190")))))
                (.ifte
                  (.name "$exprV$191")
                  (.assign
                    "expired"
                    (.unop
                      "!"
                      (.binop
                        "<"
                        (.mcall (.name "self") "timer" [])
                        (.field (.name "item") "expires"))))
                  .skip)))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.name "expired")
                  (.ret (.mcall (.name "self") "__missing__" [(.name "key")]))
                  (.ret (.callValue (.name "cache_getitem") [(.name "self"), (.name "key")])))
                .skip))) }

/-- `cachetools/__init__.py:<module>.TLRUCache.__setitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache___setitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.__setitem__"
  , params := ["key", "value", "cache_setitem"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key", "value"], isMethod := some true, defaults := [("cache_setitem", (.fnref "cachetools/__init__.py:<module>.Cache.__setitem__"))] }
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "timer"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.seq
                        (.assign "time" (.name "value_tmp0"))
                        (.seq
                          (.expr (.mcall (.name "self") "expire" [(.name "time")]))
                          (.seq
                            (.assign
                              "expires"
                              (.mcall
                                (.name "self")
                                "_TLRUCache__ttu"
                                [(.name "key"), (.name "value"), (.name "time")]))
                            (.seq
                              (.ifte
                                (.unop "!" (.binop "<" (.name "time") (.name "expires")))
                                (.ret (.mcall (.name "self") "_TLRUCache__delitem" [(.name "key")]))
                                .skip)
                              (.expr
                                (.callValue
                                  (.name "cache_setitem")
                                  [(.name "self"), (.name "key"), (.name "value")]))))))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq
              (.tryCatch
                (.setField
                  (.mcall (.name "self") "_TLRUCache__getitem" [(.name "key")])
                  "removed"
                  (.lit (.bool true)))
                "$exprV$192"
                (.ifte
                  (.inOp false (.name "$exprV$192") (.tupleE [(.lit (.str "KeyError"))]))
                  .skip
                  (.raise (.name "$exprV$192"))))
              (.seq
                .skip
                (.seq
                  (.seq
                    (.assign
                      "tmp0"
                      (.mcall
                        (.field (.name "<module>cachetools/__init__.py") "TLRUCache")
                        "_Item"
                        [(.name "key"), (.name "expires")]))
                    (.seq
                      (.setIndex
                        (.field (.name "self") "_TLRUCache__items")
                        (.name "key")
                        (.name "tmp0"))
                      (.assign "item" (.name "tmp0"))))
                  (.seq
                    .skip
                    (.seq
                      (.expr
                        (.mcall
                          (.field (.name "<module>cachetools/__init__.py") "heapq")
                          "heappush"
                          [(.field (.name "self") "_TLRUCache__order"), (.name "item")]))
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache.__delitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache___delitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.__delitem__"
  , params := ["key", "cache_delitem"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true, defaults := [("cache_delitem", (.fnref "cachetools/__init__.py:<module>.Cache.__delitem__"))] }
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "timer"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.seq
                        (.assign "time" (.name "value_tmp0"))
                        (.expr (.callValue (.name "cache_delitem") [(.name "self"), (.name "key")])))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_TLRUCache__items"))
                  (.assign "item" (.mcall (.name "tmp0") "pop" [(.name "key")])))
                (.seq
                  .skip
                  (.seq
                    (.setField (.name "item") "removed" (.lit (.bool true)))
                    (.seq
                      .skip
                      (.seq
                        (.ifte
                          (.unop "!" (.binop "<" (.name "time") (.field (.name "item") "expires")))
                          (.raise (.unop "py:exception:KeyError" (.tupleE [(.name "key")])))
                          .skip)
                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache.__iter__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache___iter__ : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.__iter__"
  , params := []
  , analysisBody := some (.seq
            (.seq
              (.assign "tmp1" (.field (.name "self") "_TLRUCache__order"))
              (.forIn
                "curr"
                (.name "tmp1")
                (.seq
                  (.assign "manager_tmp0" (.field (.name "self") "timer"))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.seq
                            (.assign "time" (.name "value_tmp0"))
                            (.seq
                              (.assign
                                "$exprV$193"
                                (.binop "<" (.name "time") (.field (.name "curr") "expires")))
                              (.seq
                                (.ifte
                                  (.name "$exprV$193")
                                  (.seq
                                    (.assign
                                      "$exprV$194"
                                      (.unop "!" (.field (.name "curr") "removed")))
                                    (.assign "$exprV$195" (.lit (.int 0))))
                                  (.seq
                                    (.assign "$exprV$194" (.name "$exprV$193"))
                                    (.assign "$exprV$195" (.lit (.int 1)))))
                                (.ifte
                                  (.name "$exprV$194")
                                  (.expr (.field (.name "curr") "key"))
                                  .skip))))
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))))
            (.seq
              .skip
              (.seq
                .skip
                (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.assign "<generator-frame>" (.alloc "<generator>" []))
            (.seq
              (.setField
                (.name "<generator-frame>")
                "<locals>"
                (.dictE [((.lit (.str "self")), (.name "self"))]))
              (.seq
                (.setField
                  (.name "<generator-frame>")
                  "<resume>"
                  (.fnref "<generator>.cachetools/__init__.py:<module>.TLRUCache.__iter__.<resume>"))
                (.seq
                  (.setField (.name "<generator-frame>") "<pc>" (.lit (.int 25)))
                  (.seq
                    (.setField (.name "<generator-frame>") "<state>" (.lit (.int 0)))
                    (.seq
                      (.setField (.name "<generator-frame>") "<return>" (.lit .unit))
                      (.seq (.ret (.name "<generator-frame>")) .skip))))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache.ttu`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache_ttu : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.ttu"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.expr (.lit (.str "The local time-to-use function used by the cache.")))
            (.ret (.field (.name "self") "_TLRUCache__ttu"))) }

/-- `cachetools/__init__.py:<module>.TLRUCache.expire`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache_expire : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.expire"
  , params := ["time"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, defaults := [("time", (.lit .unit))] }
  , body := (.seq
            (.expr
              (.lit
                (.str "Remove expired items from the cache and return an iterable of the\n        expired `(key, value)` pairs.\n\n        ")))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.isOp false (.name "time") (.lit .unit))
                  (.assign "time" (.mcall (.name "self") "timer" []))
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign "items" (.field (.name "self") "_TLRUCache__items"))
                    (.seq
                      .skip
                      (.seq
                        (.assign "order" (.field (.name "self") "_TLRUCache__order"))
                        (.seq
                          .skip
                          (.seq
                            (.ifte
                              (.binop
                                ">"
                                (.call "len" [(.name "order")])
                                (.binop
                                  "*"
                                  (.call "len" [(.name "items")])
                                  (.field (.name "self") "_TLRUCache__HEAP_CLEANUP_FACTOR")))
                              (.seq
                                (.seq
                                  (.seq
                                    (.assign "tmp0" (.listE []))
                                    (.seq
                                      (.forIn
                                        "$comp$item"
                                        (.name "order")
                                        (.seq
                                        (.ifte
                                        (.unop
                                        "!"
                                        (.unop "!" (.field (.name "$comp$item") "removed")))
                                        .cont
                                        .skip)
                                        (.expr
                                        (.mcall (.name "tmp0") "append" [(.name "$comp$item")]))))
                                      (.assign "tmp2" (.name "tmp0"))))
                                  (.seq
                                    (.setField (.name "self") "_TLRUCache__order" (.name "tmp2"))
                                    (.assign "order" (.name "tmp2"))))
                                (.expr
                                  (.mcall
                                    (.field (.name "<module>cachetools/__init__.py") "heapq")
                                    "heapify"
                                    [(.name "order")])))
                              .skip)
                            (.seq
                              .skip
                              (.seq
                                (.assign "expired" (.listE []))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign
                                      "cache_delitem"
                                      (.field
                                        (.field (.name "<module>cachetools/__init__.py") "Cache")
                                        "__delitem__"))
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign
                                        "cache_getitem"
                                        (.field
                                        (.field (.name "<module>cachetools/__init__.py") "Cache")
                                        "__getitem__"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.loop
                                        (.lit (.bool true))
                                        (.seq
                                        (.assign "$exprV$200" (.name "order"))
                                        (.seq
                                        (.ifte
                                        (.name "$exprV$200")
                                        (.seq
                                        (.assign
                                        "$exprV$197"
                                        (.field (.index (.name "order") (.lit (.int 0))) "removed"))
                                        (.seq
                                        (.ifte
                                        (.name "$exprV$197")
                                        (.seq
                                        (.assign "$exprV$198" (.name "$exprV$197"))
                                        (.assign "$exprV$199" (.lit (.int 2))))
                                        (.seq
                                        (.assign
                                        "$exprV$198"
                                        (.unop
                                        "!"
                                        (.binop
                                        "<"
                                        (.name "time")
                                        (.field (.index (.name "order") (.lit (.int 0))) "expires"))))
                                        (.assign "$exprV$199" (.lit (.int 0)))))
                                        (.seq
                                        (.assign "$exprV$201" (.name "$exprV$198"))
                                        (.assign "$exprV$202" (.name "$exprV$199")))))
                                        (.seq
                                        (.assign "$exprV$201" (.name "$exprV$200"))
                                        (.assign "$exprV$202" (.lit (.int 1)))))
                                        (.ifte
                                        (.cond
                                        (.binop "==" (.name "$exprV$202") (.lit (.int 0)))
                                        (.cond
                                        (.name "$exprV$201")
                                        (.lit (.bool true))
                                        (.lit (.bool false)))
                                        (.binop "==" (.name "$exprV$202") (.lit (.int 2))))
                                        (.seq
                                        (.assign
                                        "item"
                                        (.mcall
                                        (.field (.name "<module>cachetools/__init__.py") "heapq")
                                        "heappop"
                                        [(.name "order")]))
                                        (.ifte
                                        (.unop "!" (.field (.name "item") "removed"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.name "expired")
                                        "append"
                                        [ (.tupleE
                                        [ (.field (.name "item") "key")
                                        , (.callValue
                                        (.name "cache_getitem")
                                        [(.name "self"), (.field (.name "item") "key")]) ]) ]))
                                        (.seq
                                        (.expr
                                        (.callValue
                                        (.name "cache_delitem")
                                        [(.name "self"), (.field (.name "item") "key")]))
                                        (.delIndex (.name "items") (.field (.name "item") "key"))))
                                        .skip))
                                        .brk))))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ret (.name "expired"))
                                        (.seq .skip (.seq .skip .skip))))))))))))))))))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache.popitem`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache_popitem : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.popitem"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.expr
              (.lit
                (.str "Remove and return the `(key, value)` pair least recently used that\n        has not already expired.\n\n        ")))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "manager_tmp0" (.field (.name "self") "timer"))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.seq
                            (.assign "time" (.name "value_tmp0"))
                            (.seq
                              (.expr (.mcall (.name "self") "expire" [(.name "time")]))
                              (.seq
                                (.assign "$exprV$204" (.lit (.bool true)))
                                (.seq
                                  (.tryCatch
                                    (.assign
                                      "key"
                                      (.call
                                        "next"
                                        [ (.call "iter" [(.field (.name "self") "_TLRUCache__items")]) ]))
                                    "$exprV$203"
                                    (.seq
                                      (.assign "$exprV$204" (.lit (.bool false)))
                                      (.ifte
                                        (.inOp
                                        false
                                        (.name "$exprV$203")
                                        (.tupleE [(.lit (.str "StopIteration"))]))
                                        (.raise
                                        (.unop
                                        "py:exception:KeyError"
                                        (.tupleE
                                        [ (.binop
                                        "%"
                                        (.lit (.str "%s is empty"))
                                        (.field (.call "type" [(.name "self")]) "__name__")) ])))
                                        (.raise (.name "$exprV$203")))))
                                  (.ifte
                                    (.name "$exprV$204")
                                    (.ret
                                      (.tupleE
                                        [ (.name "key")
                                        , (.mcall (.name "self") "pop" [(.name "key")]) ]))
                                    .skip)))))
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache.clear`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache_clear : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.clear"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.expr
              (.mcall
                (.field (.name "<module>cachetools/__init__.py") "_TimedCache")
                "clear"
                [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_TLRUCache__items"))
                  (.expr (.mcall (.name "tmp0") "clear" [])))
                (.seq
                  .skip
                  (.delSlice
                    (.field (.name "self") "_TLRUCache__order")
                    (.lit .unit)
                    (.lit .unit)
                    (.lit .unit)))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache._TLRUCache__getitem`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache__TLRUCache__getitem : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache._TLRUCache__getitem"
  , params := ["key"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true }
  , body := (.seq
            (.assign "value" (.index (.field (.name "self") "_TLRUCache__items") (.name "key")))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_TLRUCache__items"))
                  (.expr (.mcall (.name "tmp0") "move_to_end" [(.name "key")])))
                (.seq .skip (.ret (.name "value")))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache._TLRUCache__delitem`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache__TLRUCache__delitem : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache._TLRUCache__delitem"
  , params := ["key", "cache_delitem"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["key"], isMethod := some true, defaults := [("cache_delitem", (.fnref "cachetools/__init__.py:<module>.Cache.__delitem__"))] }
  , body := (.seq
            (.seq
              (.assign "$exprV$206" (.lit (.bool true)))
              (.seq
                (.tryCatch
                  (.setField
                    (.mcall (.field (.name "self") "_TLRUCache__items") "pop" [(.name "key")])
                    "removed"
                    (.lit (.bool true)))
                  "$exprV$205"
                  (.seq
                    (.assign "$exprV$206" (.lit (.bool false)))
                    (.ifte
                      (.inOp false (.name "$exprV$205") (.tupleE [(.lit (.str "KeyError"))]))
                      .skip
                      (.raise (.name "$exprV$205")))))
                (.ifte
                  (.name "$exprV$206")
                  (.expr (.callValue (.name "cache_delitem") [(.name "self"), (.name "key")]))
                  .skip)))
            .skip) }

/-- `cachetools/__init__.py:<module>.cached`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__cached : Func :=
  { name := "cachetools/__init__.py:<module>.cached"
  , params := ["cache", "key", "lock", "condition", "info"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["cache"], isMethod := some false, defaults := [("key", (.fnref "cachetools/keys.py:<module>.hashkey")), ("lock", (.lit .unit)), ("condition", (.lit .unit)), ("info", (.lit (.bool false)))] }
  , body := (.seq
            (.expr
              (.lit
                (.str "Decorator to wrap a function with a memoizing callable that saves\n    results in a cache.\n\n    ")))
            (.seq
              (.assign "_wrapper" (.field (.name "<module>cachetools/_cached.py") "_wrapper"))
              (.seq
                (.assign "decorator" (.closure "cachetools/__init__.py:<module>.cached.decorator"))
                (.seq
                  .skip
                  (.seq
                    (.ret (.name "decorator"))
                    (.seq
                      .skip
                      (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))) }

/-- `cachetools/__init__.py:<module>.cached.decorator`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__cached_decorator : Func :=
  { name := "cachetools/__init__.py:<module>.cached.decorator"
  , params := ["func"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["func"], isMethod := some false }
  , body := (.seq
            (.ifte
              (.name "info")
              (.seq
                (.ifte
                  (.call
                    "isinstance"
                    [(.name "cache"), (.field (.name "<module>cachetools/__init__.py") "Cache")])
                  (.assign
                    "make_info"
                    (.closure
                      "cachetools/__init__.py:<module>.cached.decorator.make_info<redefined>0"))
                  (.ifte
                    (.call
                      "isinstance"
                      [ (.name "cache")
                      , (.field
                          (.field
                            (.field (.name "<module>cachetools/__init__.py") "collections")
                            "abc")
                          "Mapping") ])
                    (.assign
                      "make_info"
                      (.closure
                        "cachetools/__init__.py:<module>.cached.decorator.make_info<redefined>1"))
                    (.assign
                      "make_info"
                      (.fnref "cachetools/__init__.py:<module>.cached.decorator.make_info"))))
                (.ret
                  (.callValue
                    (.name "_wrapper")
                    [ (.name "func")
                    , (.name "cache")
                    , (.name "key")
                    , (.name "lock")
                    , (.name "condition")
                    , (.kwargE "info" (.name "make_info")) ])))
              (.ret
                (.callValue
                  (.name "_wrapper")
                  [ (.name "func")
                  , (.name "cache")
                  , (.name "key")
                  , (.name "lock")
                  , (.name "condition") ])))
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))) }

/-- `cachetools/__init__.py:<module>.cached.decorator.make_info<redefined>0`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__cached_decorator_make_info_redefined_0 : Func :=
  { name := "cachetools/__init__.py:<module>.cached.decorator.make_info<redefined>0"
  , params := ["hits", "misses"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["hits", "misses"], isMethod := some false }
  , body := (.seq
            (.ret
              (.callValue
                (.field (.name "<module>cachetools/__init__.py") "_CacheInfo")
                [ (.name "hits")
                , (.name "misses")
                , (.field (.name "cache") "maxsize")
                , (.field (.name "cache") "currsize") ]))
            (.seq .skip .skip)) }

/-- `cachetools/__init__.py:<module>.cached.decorator.make_info<redefined>1`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__cached_decorator_make_info_redefined_1 : Func :=
  { name := "cachetools/__init__.py:<module>.cached.decorator.make_info<redefined>1"
  , params := ["hits", "misses"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["hits", "misses"], isMethod := some false }
  , body := (.seq
            (.ret
              (.callValue
                (.field (.name "<module>cachetools/__init__.py") "_CacheInfo")
                [(.name "hits"), (.name "misses"), (.lit .unit), (.call "len" [(.name "cache")])]))
            (.seq .skip (.seq .skip .skip))) }

/-- `cachetools/__init__.py:<module>.cached.decorator.make_info`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__cached_decorator_make_info : Func :=
  { name := "cachetools/__init__.py:<module>.cached.decorator.make_info"
  , params := ["hits", "misses"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["hits", "misses"], isMethod := some false }
  , body := (.seq
            (.ret
              (.callValue
                (.field (.name "<module>cachetools/__init__.py") "_CacheInfo")
                [(.name "hits"), (.name "misses"), (.lit (.int 0)), (.lit (.int 0))]))
            .skip) }

/-- `cachetools/__init__.py:<module>.cachedmethod`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__cachedmethod : Func :=
  { name := "cachetools/__init__.py:<module>.cachedmethod"
  , params := ["cache", "key", "lock", "condition", "info"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["cache"], isMethod := some false, defaults := [("key", (.fnref "cachetools/keys.py:<module>.methodkey")), ("lock", (.lit .unit)), ("condition", (.lit .unit)), ("info", (.lit (.bool false)))] }
  , body := (.seq
            (.expr
              (.lit
                (.str "Decorator to wrap a method with a memoizing callable that saves\n    results in a cache.\n\n    ")))
            (.seq
              (.assign "_wrapper" (.field (.name "<module>cachetools/_cachedmethod.py") "_wrapper"))
              (.seq
                (.assign
                  "decorator"
                  (.closure "cachetools/__init__.py:<module>.cachedmethod.decorator"))
                (.seq
                  .skip
                  (.seq
                    (.ret (.name "decorator"))
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))) }

/-- `cachetools/__init__.py:<module>.cachedmethod.decorator`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__cachedmethod_decorator : Func :=
  { name := "cachetools/__init__.py:<module>.cachedmethod.decorator"
  , params := ["method"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["method"], isMethod := some false }
  , body := (.seq
            (.ifte
              (.name "info")
              (.seq
                (.assign
                  "make_info"
                  (.fnref "cachetools/__init__.py:<module>.cachedmethod.decorator.make_info"))
                (.ret
                  (.callValue
                    (.name "_wrapper")
                    [ (.name "method")
                    , (.name "cache")
                    , (.name "key")
                    , (.name "lock")
                    , (.name "condition")
                    , (.kwargE "info" (.name "make_info")) ])))
              (.ret
                (.callValue
                  (.name "_wrapper")
                  [ (.name "method")
                  , (.name "cache")
                  , (.name "key")
                  , (.name "lock")
                  , (.name "condition") ])))
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))) }

/-- `cachetools/__init__.py:<module>.cachedmethod.decorator.make_info`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__cachedmethod_decorator_make_info : Func :=
  { name := "cachetools/__init__.py:<module>.cachedmethod.decorator.make_info"
  , params := ["cache", "hits", "misses"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["cache", "hits", "misses"], isMethod := some false }
  , body := (.seq
            (.ifte
              (.call
                "isinstance"
                [(.name "cache"), (.field (.name "<module>cachetools/__init__.py") "Cache")])
              (.ret
                (.callValue
                  (.field (.name "<module>cachetools/__init__.py") "_CacheInfo")
                  [ (.name "hits")
                  , (.name "misses")
                  , (.field (.name "cache") "maxsize")
                  , (.field (.name "cache") "currsize") ]))
              (.ifte
                (.call
                  "isinstance"
                  [ (.name "cache")
                  , (.field
                      (.field (.field (.name "<module>cachetools/__init__.py") "collections") "abc")
                      "Mapping") ])
                (.ret
                  (.callValue
                    (.field (.name "<module>cachetools/__init__.py") "_CacheInfo")
                    [ (.name "hits")
                    , (.name "misses")
                    , (.lit .unit)
                    , (.call "len" [(.name "cache")]) ]))
                (.raise
                  (.unop
                    "py:exception:TypeError"
                    (.tupleE [(.lit (.str "cache(self) must return a mutable mapping"))])))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/_cached.py:<module>._condition_info`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___condition_info : Func :=
  { name := "cachetools/_cached.py:<module>._condition_info"
  , params := ["func", "cache", "key", "lock", "cond", "info"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["func", "cache", "key", "lock", "cond", "info"], isMethod := some false }
  , body := (.seq
            (.assign "hits" (.boxNew (.lit .unit)))
            (.seq
              (.assign "misses" (.boxNew (.lit .unit)))
              (.seq
                (.seq
                  (.assign "tmp0" (.lit (.int 0)))
                  (.seq
                    (.setField (.name "hits") "v" (.name "tmp0"))
                    (.setField (.name "misses") "v" (.name "tmp0"))))
                (.seq
                  (.assign "pending" (.call "set" []))
                  (.seq
                    (.assign
                      "wrapper"
                      (.closure "cachetools/_cached.py:<module>._condition_info.wrapper"))
                    (.seq
                      (.assign
                        "cache_clear"
                        (.closure "cachetools/_cached.py:<module>._condition_info.cache_clear"))
                      (.seq
                        (.assign
                          "cache_info"
                          (.closure "cachetools/_cached.py:<module>._condition_info.cache_info"))
                        (.seq
                          (.setField (.name "wrapper") "cache_clear" (.name "cache_clear"))
                          (.seq
                            (.setField (.name "wrapper") "cache_info" (.name "cache_info"))
                            (.seq
                              .skip
                              (.seq
                                (.ret (.name "wrapper"))
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))) }

/-- `cachetools/_cached.py:<module>._condition_info.wrapper`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___condition_info_wrapper : Func :=
  { name := "cachetools/_cached.py:<module>._condition_info.wrapper"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            .skip
            (.seq
              (.assign
                "k"
                (.callValue (.name "key") [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
              (.seq
                (.seq
                  (.assign "manager_tmp0" (.name "lock"))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.seq
                            (.expr
                              (.mcall
                                (.name "cond")
                                "wait_for"
                                [ (.closure
                                    "cachetools/_cached.py:<module>._condition_info.wrapper.<lambda>0") ]))
                            (.tryCatch
                              (.seq
                                (.assign "result" (.index (.name "cache") (.name "k")))
                                (.seq
                                  (.setField
                                    (.name "hits")
                                    "v"
                                    (.binop "+" (.field (.name "hits") "v") (.lit (.int 1))))
                                  (.ret (.name "result"))))
                              "$exprV$207"
                              (.ifte
                                (.inOp
                                  false
                                  (.name "$exprV$207")
                                  (.tupleE [(.lit (.str "KeyError"))]))
                                (.seq
                                  (.expr (.mcall (.name "pending") "add" [(.name "k")]))
                                  (.setField
                                    (.name "misses")
                                    "v"
                                    (.binop "+" (.field (.name "misses") "v") (.lit (.int 1)))))
                                (.raise (.name "$exprV$207")))))
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                (.seq
                  .skip
                  (.seq
                    (.tryFinally
                      (.seq
                        (.assign
                          "v"
                          (.callValue
                            (.name "func")
                            [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                        (.seq
                          (.assign "manager_tmp1" (.name "lock"))
                          (.seq
                            (.assign "enter_tmp1" (.field (.name "manager_tmp1") "__enter__"))
                            (.seq
                              (.assign "exit_tmp1" (.field (.name "manager_tmp1") "__exit__"))
                              (.seq
                                (.assign
                                  "value_tmp1"
                                  (.mcall (.name "manager_tmp1") "__enter__" []))
                                (.tryFinally
                                  (.seq
                                    (.tryCatch
                                      (.setIndex (.name "cache") (.name "k") (.name "v"))
                                      "$exprV$208"
                                      (.ifte
                                        (.inOp
                                        false
                                        (.name "$exprV$208")
                                        (.tupleE [(.lit (.str "ValueError"))]))
                                        .skip
                                        (.raise (.name "$exprV$208"))))
                                    (.ret (.name "v")))
                                  (.expr (.mcall (.name "manager_tmp1") "__exit__" []))))))))
                      (.seq
                        (.assign "manager_tmp2" (.name "lock"))
                        (.seq
                          (.assign "enter_tmp2" (.field (.name "manager_tmp2") "__enter__"))
                          (.seq
                            (.assign "exit_tmp2" (.field (.name "manager_tmp2") "__exit__"))
                            (.seq
                              (.assign "value_tmp2" (.mcall (.name "manager_tmp2") "__enter__" []))
                              (.tryFinally
                                (.seq
                                  (.expr (.mcall (.name "pending") "remove" [(.name "k")]))
                                  (.expr (.mcall (.name "cond") "notify_all" [])))
                                (.expr (.mcall (.name "manager_tmp2") "__exit__" []))))))))
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))))))))))))))) }

/-- `cachetools/_cached.py:<module>._condition_info.wrapper.<lambda>0`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___condition_info_wrapper__lambda_0 : Func :=
  { name := "cachetools/_cached.py:<module>._condition_info.wrapper.<lambda>0"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq (.ret (.inOp true (.name "k") (.name "pending"))) (.seq .skip .skip)) }

/-- `cachetools/_cached.py:<module>._condition_info.cache_clear`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___condition_info_cache_clear : Func :=
  { name := "cachetools/_cached.py:<module>._condition_info.cache_clear"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "manager_tmp0" (.name "lock"))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.seq
                            (.expr (.mcall (.name "cache") "clear" []))
                            (.seq
                              (.assign "tmp0" (.lit (.int 0)))
                              (.seq
                                (.setField (.name "hits") "v" (.name "tmp0"))
                                (.setField (.name "misses") "v" (.name "tmp0")))))
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))) }

/-- `cachetools/_cached.py:<module>._condition_info.cache_info`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___condition_info_cache_info : Func :=
  { name := "cachetools/_cached.py:<module>._condition_info.cache_info"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.name "lock"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.ret (.callValue (.name "info") [(.name "hits"), (.name "misses")]))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq
              .skip
              (.seq
                .skip
                (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))) }

/-- `cachetools/_cached.py:<module>._locked_info`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___locked_info : Func :=
  { name := "cachetools/_cached.py:<module>._locked_info"
  , params := ["func", "cache", "key", "lock", "info"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["func", "cache", "key", "lock", "info"], isMethod := some false }
  , body := (.seq
            (.assign "hits" (.boxNew (.lit .unit)))
            (.seq
              (.assign "misses" (.boxNew (.lit .unit)))
              (.seq
                (.seq
                  (.assign "tmp0" (.lit (.int 0)))
                  (.seq
                    (.setField (.name "hits") "v" (.name "tmp0"))
                    (.setField (.name "misses") "v" (.name "tmp0"))))
                (.seq
                  (.assign
                    "wrapper"
                    (.closure "cachetools/_cached.py:<module>._locked_info.wrapper"))
                  (.seq
                    (.assign
                      "cache_clear"
                      (.closure "cachetools/_cached.py:<module>._locked_info.cache_clear"))
                    (.seq
                      (.assign
                        "cache_info"
                        (.closure "cachetools/_cached.py:<module>._locked_info.cache_info"))
                      (.seq
                        (.setField (.name "wrapper") "cache_clear" (.name "cache_clear"))
                        (.seq
                          (.setField (.name "wrapper") "cache_info" (.name "cache_info"))
                          (.seq
                            (.ret (.name "wrapper"))
                            (.seq
                              .skip
                              (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))) }

/-- `cachetools/_cached.py:<module>._locked_info.wrapper`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___locked_info_wrapper : Func :=
  { name := "cachetools/_cached.py:<module>._locked_info.wrapper"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign
                  "k"
                  (.callValue
                    (.name "key")
                    [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                (.seq
                  .skip
                  (.seq
                    (.seq
                      (.assign "manager_tmp0" (.name "lock"))
                      (.seq
                        (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                        (.seq
                          (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                          (.seq
                            (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                            (.tryFinally
                              (.tryCatch
                                (.seq
                                  (.assign "result" (.index (.name "cache") (.name "k")))
                                  (.seq
                                    (.setField
                                      (.name "hits")
                                      "v"
                                      (.binop "+" (.field (.name "hits") "v") (.lit (.int 1))))
                                    (.ret (.name "result"))))
                                "$exprV$209"
                                (.ifte
                                  (.inOp
                                    false
                                    (.name "$exprV$209")
                                    (.tupleE [(.lit (.str "KeyError"))]))
                                  (.setField
                                    (.name "misses")
                                    "v"
                                    (.binop "+" (.field (.name "misses") "v") (.lit (.int 1))))
                                  (.raise (.name "$exprV$209"))))
                              (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "v"
                          (.callValue
                            (.name "func")
                            [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                        (.seq
                          .skip
                          (.seq
                            (.seq
                              (.assign "manager_tmp1" (.name "lock"))
                              (.seq
                                (.assign "enter_tmp1" (.field (.name "manager_tmp1") "__enter__"))
                                (.seq
                                  (.assign "exit_tmp1" (.field (.name "manager_tmp1") "__exit__"))
                                  (.seq
                                    (.assign
                                      "value_tmp1"
                                      (.mcall (.name "manager_tmp1") "__enter__" []))
                                    (.tryFinally
                                      (.tryCatch
                                        (.ret
                                        (.mcall
                                        (.name "cache")
                                        "setdefault"
                                        [(.name "k"), (.name "v")]))
                                        "$exprV$210"
                                        (.ifte
                                        (.inOp
                                        false
                                        (.name "$exprV$210")
                                        (.tupleE [(.lit (.str "ValueError"))]))
                                        (.ret (.name "v"))
                                        (.raise (.name "$exprV$210"))))
                                      (.expr (.mcall (.name "manager_tmp1") "__exit__" [])))))))
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))))))) }

/-- `cachetools/_cached.py:<module>._locked_info.cache_clear`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___locked_info_cache_clear : Func :=
  { name := "cachetools/_cached.py:<module>._locked_info.cache_clear"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "manager_tmp0" (.name "lock"))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.seq
                            (.expr (.mcall (.name "cache") "clear" []))
                            (.seq
                              (.assign "tmp0" (.lit (.int 0)))
                              (.seq
                                (.setField (.name "hits") "v" (.name "tmp0"))
                                (.setField (.name "misses") "v" (.name "tmp0")))))
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))) }

/-- `cachetools/_cached.py:<module>._locked_info.cache_info`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___locked_info_cache_info : Func :=
  { name := "cachetools/_cached.py:<module>._locked_info.cache_info"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.name "lock"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.ret (.callValue (.name "info") [(.name "hits"), (.name "misses")]))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq
              .skip
              (.seq
                .skip
                (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))) }

/-- `cachetools/_cached.py:<module>._unlocked_info`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___unlocked_info : Func :=
  { name := "cachetools/_cached.py:<module>._unlocked_info"
  , params := ["func", "cache", "key", "info"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["func", "cache", "key", "info"], isMethod := some false }
  , body := (.seq
            (.assign "hits" (.boxNew (.lit .unit)))
            (.seq
              (.assign "misses" (.boxNew (.lit .unit)))
              (.seq
                (.seq
                  (.assign "tmp0" (.lit (.int 0)))
                  (.seq
                    (.setField (.name "hits") "v" (.name "tmp0"))
                    (.setField (.name "misses") "v" (.name "tmp0"))))
                (.seq
                  (.assign
                    "wrapper"
                    (.closure "cachetools/_cached.py:<module>._unlocked_info.wrapper"))
                  (.seq
                    (.assign
                      "cache_clear"
                      (.closure "cachetools/_cached.py:<module>._unlocked_info.cache_clear"))
                    (.seq
                      (.assign
                        "cache_info"
                        (.closure "cachetools/_cached.py:<module>._unlocked_info.cache_info"))
                      (.seq
                        (.setField (.name "wrapper") "cache_clear" (.name "cache_clear"))
                        (.seq
                          (.setField (.name "wrapper") "cache_info" (.name "cache_info"))
                          (.seq
                            (.ret (.name "wrapper"))
                            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))) }

/-- `cachetools/_cached.py:<module>._unlocked_info.wrapper`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___unlocked_info_wrapper : Func :=
  { name := "cachetools/_cached.py:<module>._unlocked_info.wrapper"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign
                  "k"
                  (.callValue
                    (.name "key")
                    [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                (.seq
                  .skip
                  (.seq
                    (.tryCatch
                      (.seq
                        (.assign "result" (.index (.name "cache") (.name "k")))
                        (.seq
                          (.setField
                            (.name "hits")
                            "v"
                            (.binop "+" (.field (.name "hits") "v") (.lit (.int 1))))
                          (.ret (.name "result"))))
                      "$exprV$211"
                      (.ifte
                        (.inOp false (.name "$exprV$211") (.tupleE [(.lit (.str "KeyError"))]))
                        (.setField
                          (.name "misses")
                          "v"
                          (.binop "+" (.field (.name "misses") "v") (.lit (.int 1))))
                        (.raise (.name "$exprV$211"))))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "v"
                          (.callValue
                            (.name "func")
                            [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                        (.seq
                          .skip
                          (.seq
                            (.tryCatch
                              (.setIndex (.name "cache") (.name "k") (.name "v"))
                              "$exprV$212"
                              (.ifte
                                (.inOp
                                  false
                                  (.name "$exprV$212")
                                  (.tupleE [(.lit (.str "ValueError"))]))
                                .skip
                                (.raise (.name "$exprV$212"))))
                            (.seq .skip (.seq (.ret (.name "v")) (.seq .skip (.seq .skip .skip))))))))))))) }

/-- `cachetools/_cached.py:<module>._unlocked_info.cache_clear`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___unlocked_info_cache_clear : Func :=
  { name := "cachetools/_cached.py:<module>._unlocked_info.cache_clear"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.expr (.mcall (.name "cache") "clear" []))
                (.seq
                  .skip
                  (.seq
                    (.seq
                      (.assign "tmp0" (.lit (.int 0)))
                      (.seq
                        (.setField (.name "hits") "v" (.name "tmp0"))
                        (.setField (.name "misses") "v" (.name "tmp0"))))
                    (.seq .skip .skip)))))) }

/-- `cachetools/_cached.py:<module>._unlocked_info.cache_info`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___unlocked_info_cache_info : Func :=
  { name := "cachetools/_cached.py:<module>._unlocked_info.cache_info"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            (.ret (.callValue (.name "info") [(.name "hits"), (.name "misses")]))
            (.seq .skip (.seq .skip .skip))) }

/-- `cachetools/_cached.py:<module>._uncached_info`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___uncached_info : Func :=
  { name := "cachetools/_cached.py:<module>._uncached_info"
  , params := ["func", "info"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["func", "info"], isMethod := some false }
  , body := (.seq
            (.assign "misses" (.boxNew (.lit .unit)))
            (.seq
              (.setField (.name "misses") "v" (.lit (.int 0)))
              (.seq
                (.assign
                  "wrapper"
                  (.closure "cachetools/_cached.py:<module>._uncached_info.wrapper"))
                (.seq
                  (.assign
                    "cache_clear"
                    (.closure "cachetools/_cached.py:<module>._uncached_info.cache_clear"))
                  (.seq
                    (.setField (.name "wrapper") "cache_clear" (.name "cache_clear"))
                    (.seq
                      (.setField
                        (.name "wrapper")
                        "cache_info"
                        (.closure "cachetools/_cached.py:<module>._uncached_info.<lambda>1"))
                      (.seq (.ret (.name "wrapper")) (.seq .skip (.seq .skip .skip))))))))) }

/-- `cachetools/_cached.py:<module>._uncached_info.wrapper`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___uncached_info_wrapper : Func :=
  { name := "cachetools/_cached.py:<module>._uncached_info.wrapper"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.setField
                  (.name "misses")
                  "v"
                  (.binop "+" (.field (.name "misses") "v") (.lit (.int 1))))
                (.seq
                  .skip
                  (.ret
                    (.callValue
                      (.name "func")
                      [(.starred (.name "args")), (.dstarred (.name "kwargs"))])))))) }

/-- `cachetools/_cached.py:<module>._uncached_info.cache_clear`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___uncached_info_cache_clear : Func :=
  { name := "cachetools/_cached.py:<module>._uncached_info.cache_clear"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq .skip (.seq .skip (.setField (.name "misses") "v" (.lit (.int 0))))) }

/-- `cachetools/_cached.py:<module>._uncached_info.<lambda>1`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___uncached_info__lambda_1 : Func :=
  { name := "cachetools/_cached.py:<module>._uncached_info.<lambda>1"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            (.ret (.callValue (.name "info") [(.lit (.int 0)), (.name "misses")]))
            (.seq .skip .skip)) }

/-- `cachetools/_cached.py:<module>._condition`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___condition : Func :=
  { name := "cachetools/_cached.py:<module>._condition"
  , params := ["func", "cache", "key", "lock", "cond"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["func", "cache", "key", "lock", "cond"], isMethod := some false }
  , body := (.seq
            (.assign "pending" (.call "set" []))
            (.seq
              (.assign "wrapper" (.closure "cachetools/_cached.py:<module>._condition.wrapper"))
              (.seq
                (.assign
                  "cache_clear"
                  (.closure "cachetools/_cached.py:<module>._condition.cache_clear"))
                (.seq
                  (.setField (.name "wrapper") "cache_clear" (.name "cache_clear"))
                  (.seq
                    (.ret (.name "wrapper"))
                    (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))) }

/-- `cachetools/_cached.py:<module>._condition.wrapper`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___condition_wrapper : Func :=
  { name := "cachetools/_cached.py:<module>._condition.wrapper"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            (.assign
              "k"
              (.callValue (.name "key") [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
            (.seq
              (.seq
                (.assign "manager_tmp0" (.name "lock"))
                (.seq
                  (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                  (.seq
                    (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                    (.seq
                      (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                      (.tryFinally
                        (.seq
                          (.expr
                            (.mcall
                              (.name "cond")
                              "wait_for"
                              [ (.closure
                                  "cachetools/_cached.py:<module>._condition.wrapper.<lambda>2") ]))
                          (.tryCatch
                            (.seq
                              (.assign "result" (.index (.name "cache") (.name "k")))
                              (.ret (.name "result")))
                            "$exprV$213"
                            (.ifte
                              (.inOp
                                false
                                (.name "$exprV$213")
                                (.tupleE [(.lit (.str "KeyError"))]))
                              (.expr (.mcall (.name "pending") "add" [(.name "k")]))
                              (.raise (.name "$exprV$213")))))
                        (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
              (.seq
                (.tryFinally
                  (.seq
                    (.assign
                      "v"
                      (.callValue
                        (.name "func")
                        [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                    (.seq
                      (.assign "manager_tmp1" (.name "lock"))
                      (.seq
                        (.assign "enter_tmp1" (.field (.name "manager_tmp1") "__enter__"))
                        (.seq
                          (.assign "exit_tmp1" (.field (.name "manager_tmp1") "__exit__"))
                          (.seq
                            (.assign "value_tmp1" (.mcall (.name "manager_tmp1") "__enter__" []))
                            (.tryFinally
                              (.seq
                                (.tryCatch
                                  (.setIndex (.name "cache") (.name "k") (.name "v"))
                                  "$exprV$214"
                                  (.ifte
                                    (.inOp
                                      false
                                      (.name "$exprV$214")
                                      (.tupleE [(.lit (.str "ValueError"))]))
                                    .skip
                                    (.raise (.name "$exprV$214"))))
                                (.ret (.name "v")))
                              (.expr (.mcall (.name "manager_tmp1") "__exit__" []))))))))
                  (.seq
                    (.assign "manager_tmp2" (.name "lock"))
                    (.seq
                      (.assign "enter_tmp2" (.field (.name "manager_tmp2") "__enter__"))
                      (.seq
                        (.assign "exit_tmp2" (.field (.name "manager_tmp2") "__exit__"))
                        (.seq
                          (.assign "value_tmp2" (.mcall (.name "manager_tmp2") "__enter__" []))
                          (.tryFinally
                            (.seq
                              (.expr (.mcall (.name "pending") "remove" [(.name "k")]))
                              (.expr (.mcall (.name "cond") "notify_all" [])))
                            (.expr (.mcall (.name "manager_tmp2") "__exit__" []))))))))
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))))))))) }

/-- `cachetools/_cached.py:<module>._condition.wrapper.<lambda>2`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___condition_wrapper__lambda_2 : Func :=
  { name := "cachetools/_cached.py:<module>._condition.wrapper.<lambda>2"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq (.ret (.inOp true (.name "k") (.name "pending"))) (.seq .skip .skip)) }

/-- `cachetools/_cached.py:<module>._condition.cache_clear`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___condition_cache_clear : Func :=
  { name := "cachetools/_cached.py:<module>._condition.cache_clear"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.name "lock"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.expr (.mcall (.name "cache") "clear" []))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))) }

/-- `cachetools/_cached.py:<module>._locked`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___locked : Func :=
  { name := "cachetools/_cached.py:<module>._locked"
  , params := ["func", "cache", "key", "lock"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["func", "cache", "key", "lock"], isMethod := some false }
  , body := (.seq
            (.assign "wrapper" (.closure "cachetools/_cached.py:<module>._locked.wrapper"))
            (.seq
              (.assign
                "cache_clear"
                (.closure "cachetools/_cached.py:<module>._locked.cache_clear"))
              (.seq
                (.setField (.name "wrapper") "cache_clear" (.name "cache_clear"))
                (.seq (.ret (.name "wrapper")) (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/_cached.py:<module>._locked.wrapper`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___locked_wrapper : Func :=
  { name := "cachetools/_cached.py:<module>._locked.wrapper"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            (.assign
              "k"
              (.callValue (.name "key") [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "manager_tmp0" (.name "lock"))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.tryCatch
                            (.ret (.index (.name "cache") (.name "k")))
                            "$exprV$215"
                            (.ifte
                              (.inOp
                                false
                                (.name "$exprV$215")
                                (.tupleE [(.lit (.str "KeyError"))]))
                              .skip
                              (.raise (.name "$exprV$215"))))
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "v"
                      (.callValue
                        (.name "func")
                        [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                    (.seq
                      .skip
                      (.seq
                        (.seq
                          (.assign "manager_tmp1" (.name "lock"))
                          (.seq
                            (.assign "enter_tmp1" (.field (.name "manager_tmp1") "__enter__"))
                            (.seq
                              (.assign "exit_tmp1" (.field (.name "manager_tmp1") "__exit__"))
                              (.seq
                                (.assign
                                  "value_tmp1"
                                  (.mcall (.name "manager_tmp1") "__enter__" []))
                                (.tryFinally
                                  (.tryCatch
                                    (.ret
                                      (.mcall
                                        (.name "cache")
                                        "setdefault"
                                        [(.name "k"), (.name "v")]))
                                    "$exprV$216"
                                    (.ifte
                                      (.inOp
                                        false
                                        (.name "$exprV$216")
                                        (.tupleE [(.lit (.str "ValueError"))]))
                                      (.ret (.name "v"))
                                      (.raise (.name "$exprV$216"))))
                                  (.expr (.mcall (.name "manager_tmp1") "__exit__" [])))))))
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))) }

/-- `cachetools/_cached.py:<module>._locked.cache_clear`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___locked_cache_clear : Func :=
  { name := "cachetools/_cached.py:<module>._locked.cache_clear"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.name "lock"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.expr (.mcall (.name "cache") "clear" []))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))) }

/-- `cachetools/_cached.py:<module>._unlocked`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___unlocked : Func :=
  { name := "cachetools/_cached.py:<module>._unlocked"
  , params := ["func", "cache", "key"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["func", "cache", "key"], isMethod := some false }
  , body := (.seq
            (.assign "wrapper" (.closure "cachetools/_cached.py:<module>._unlocked.wrapper"))
            (.seq
              (.setField
                (.name "wrapper")
                "cache_clear"
                (.closure "cachetools/_cached.py:<module>._unlocked.<lambda>3"))
              (.seq (.ret (.name "wrapper")) .skip))) }

/-- `cachetools/_cached.py:<module>._unlocked.wrapper`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___unlocked_wrapper : Func :=
  { name := "cachetools/_cached.py:<module>._unlocked.wrapper"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            (.assign
              "k"
              (.callValue (.name "key") [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
            (.seq
              .skip
              (.seq
                (.tryCatch
                  (.ret (.index (.name "cache") (.name "k")))
                  "$exprV$217"
                  (.ifte
                    (.inOp false (.name "$exprV$217") (.tupleE [(.lit (.str "KeyError"))]))
                    .skip
                    (.raise (.name "$exprV$217"))))
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "v"
                      (.callValue
                        (.name "func")
                        [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                    (.seq
                      .skip
                      (.seq
                        (.tryCatch
                          (.setIndex (.name "cache") (.name "k") (.name "v"))
                          "$exprV$218"
                          (.ifte
                            (.inOp
                              false
                              (.name "$exprV$218")
                              (.tupleE [(.lit (.str "ValueError"))]))
                            .skip
                            (.raise (.name "$exprV$218"))))
                        (.seq .skip (.seq (.ret (.name "v")) .skip))))))))) }

/-- `cachetools/_cached.py:<module>._unlocked.<lambda>3`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___unlocked__lambda_3 : Func :=
  { name := "cachetools/_cached.py:<module>._unlocked.<lambda>3"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq (.ret (.mcall (.name "cache") "clear" [])) .skip) }

/-- `cachetools/_cached.py:<module>._uncached`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___uncached : Func :=
  { name := "cachetools/_cached.py:<module>._uncached"
  , params := ["func"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["func"], isMethod := some false }
  , body := (.seq
            (.assign "wrapper" (.closure "cachetools/_cached.py:<module>._uncached.wrapper"))
            (.seq
              (.setField
                (.name "wrapper")
                "cache_clear"
                (.fnref "cachetools/_cached.py:<module>._uncached.<lambda>4"))
              (.seq (.ret (.name "wrapper")) .skip))) }

/-- `cachetools/_cached.py:<module>._uncached.wrapper`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___uncached_wrapper : Func :=
  { name := "cachetools/_cached.py:<module>._uncached.wrapper"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            (.ret
              (.callValue (.name "func") [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
            .skip) }

/-- `cachetools/_cached.py:<module>._uncached.<lambda>4`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___uncached__lambda_4 : Func :=
  { name := "cachetools/_cached.py:<module>._uncached.<lambda>4"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.ret (.lit .unit)) }

/-- `cachetools/_cached.py:<module>._wrapper`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___wrapper : Func :=
  { name := "cachetools/_cached.py:<module>._wrapper"
  , params := ["func", "cache", "key", "lock", "cond", "info"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["func", "cache", "key"], isMethod := some false, defaults := [("lock", (.lit .unit)), ("cond", (.lit .unit)), ("info", (.lit .unit))] }
  , body := (.seq
            (.ifte
              (.isOp true (.name "info") (.lit .unit))
              (.ifte
                (.isOp false (.name "cache") (.lit .unit))
                (.assign
                  "wrapper"
                  (.callValue
                    (.field (.name "<module>cachetools/_cached.py") "_uncached_info")
                    [(.name "func"), (.name "info")]))
                (.seq
                  (.assign "$exprV$219" (.isOp true (.name "cond") (.lit .unit)))
                  (.seq
                    (.ifte
                      (.name "$exprV$219")
                      (.seq
                        (.assign "$exprV$220" (.isOp true (.name "lock") (.lit .unit)))
                        (.assign "$exprV$221" (.lit (.int 0))))
                      (.seq
                        (.assign "$exprV$220" (.name "$exprV$219"))
                        (.assign "$exprV$221" (.lit (.int 1)))))
                    (.ifte
                      (.cond
                        (.binop "==" (.name "$exprV$221") (.lit (.int 0)))
                        (.cond (.name "$exprV$220") (.lit (.bool true)) (.lit (.bool false)))
                        (.binop "==" (.name "$exprV$221") (.lit (.int 2))))
                      (.assign
                        "wrapper"
                        (.callValue
                          (.field (.name "<module>cachetools/_cached.py") "_condition_info")
                          [ (.name "func")
                          , (.name "cache")
                          , (.name "key")
                          , (.name "lock")
                          , (.name "cond")
                          , (.name "info") ]))
                      (.ifte
                        (.isOp true (.name "cond") (.lit .unit))
                        (.assign
                          "wrapper"
                          (.callValue
                            (.field (.name "<module>cachetools/_cached.py") "_condition_info")
                            [ (.name "func")
                            , (.name "cache")
                            , (.name "key")
                            , (.name "cond")
                            , (.name "cond")
                            , (.name "info") ]))
                        (.ifte
                          (.isOp true (.name "lock") (.lit .unit))
                          (.assign
                            "wrapper"
                            (.callValue
                              (.field (.name "<module>cachetools/_cached.py") "_locked_info")
                              [ (.name "func")
                              , (.name "cache")
                              , (.name "key")
                              , (.name "lock")
                              , (.name "info") ]))
                          (.assign
                            "wrapper"
                            (.callValue
                              (.field (.name "<module>cachetools/_cached.py") "_unlocked_info")
                              [(.name "func"), (.name "cache"), (.name "key"), (.name "info")]))))))))
              (.seq
                (.ifte
                  (.isOp false (.name "cache") (.lit .unit))
                  (.assign
                    "wrapper"
                    (.callValue
                      (.field (.name "<module>cachetools/_cached.py") "_uncached")
                      [(.name "func")]))
                  (.seq
                    (.assign "$exprV$222" (.isOp true (.name "cond") (.lit .unit)))
                    (.seq
                      (.ifte
                        (.name "$exprV$222")
                        (.seq
                          (.assign "$exprV$223" (.isOp true (.name "lock") (.lit .unit)))
                          (.assign "$exprV$224" (.lit (.int 0))))
                        (.seq
                          (.assign "$exprV$223" (.name "$exprV$222"))
                          (.assign "$exprV$224" (.lit (.int 1)))))
                      (.ifte
                        (.cond
                          (.binop "==" (.name "$exprV$224") (.lit (.int 0)))
                          (.cond (.name "$exprV$223") (.lit (.bool true)) (.lit (.bool false)))
                          (.binop "==" (.name "$exprV$224") (.lit (.int 2))))
                        (.assign
                          "wrapper"
                          (.callValue
                            (.field (.name "<module>cachetools/_cached.py") "_condition")
                            [ (.name "func")
                            , (.name "cache")
                            , (.name "key")
                            , (.name "lock")
                            , (.name "cond") ]))
                        (.ifte
                          (.isOp true (.name "cond") (.lit .unit))
                          (.assign
                            "wrapper"
                            (.callValue
                              (.field (.name "<module>cachetools/_cached.py") "_condition")
                              [ (.name "func")
                              , (.name "cache")
                              , (.name "key")
                              , (.name "cond")
                              , (.name "cond") ]))
                          (.ifte
                            (.isOp true (.name "lock") (.lit .unit))
                            (.assign
                              "wrapper"
                              (.callValue
                                (.field (.name "<module>cachetools/_cached.py") "_locked")
                                [(.name "func"), (.name "cache"), (.name "key"), (.name "lock")]))
                            (.assign
                              "wrapper"
                              (.callValue
                                (.field (.name "<module>cachetools/_cached.py") "_unlocked")
                                [(.name "func"), (.name "cache"), (.name "key")]))))))))
                (.setField (.name "wrapper") "cache_info" (.lit .unit))))
            (.seq
              .skip
              (.seq
                (.setField (.name "wrapper") "cache" (.name "cache"))
                (.seq
                  .skip
                  (.seq
                    (.setField (.name "wrapper") "cache_key" (.name "key"))
                    (.seq
                      .skip
                      (.seq
                        (.setField
                          (.name "wrapper")
                          "cache_lock"
                          (.cond
                            (.isOp true (.name "lock") (.lit .unit))
                            (.name "lock")
                            (.name "cond")))
                        (.seq
                          .skip
                          (.seq
                            (.setField (.name "wrapper") "cache_condition" (.name "cond"))
                            (.seq
                              .skip
                              (.seq
                                (.ret
                                  (.mcall
                                    (.field (.name "<module>cachetools/_cached.py") "functools")
                                    "update_wrapper"
                                    [(.name "wrapper"), (.name "func")]))
                                (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._warn_classmethod`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___warn_classmethod : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._warn_classmethod"
  , params := ["stacklevel"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["stacklevel"], isMethod := some false }
  , body := (.seq
            (.expr
              (.mcall
                (.field (.name "<module>cachetools/_cachedmethod.py") "warnings")
                "warn"
                [ (.lit (.str "decorating class methods with @cachedmethod is deprecated"))
                , (.name "DeprecationWarning")
                , (.kwargE "stacklevel" (.name "stacklevel")) ]))
            (.seq .skip .skip)) }

/-- `cachetools/_cachedmethod.py:<module>._warn_instance_dict`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___warn_instance_dict : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._warn_instance_dict"
  , params := ["msg", "stacklevel"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["msg", "stacklevel"], isMethod := some false }
  , body := (.seq
            (.expr
              (.mcall
                (.field (.name "<module>cachetools/_cachedmethod.py") "warnings")
                "warn"
                [ (.name "msg")
                , (.name "DeprecationWarning")
                , (.kwargE "stacklevel" (.name "stacklevel")) ]))
            (.seq .skip .skip)) }

/-- `cachetools/_cachedmethod.py:<module>._none`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___none : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._none"
  , params := ["_"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["_"], isMethod := some false }
  , body := (.ret (.lit .unit)) }

/-- `cachetools/_cachedmethod.py:<module>._WrapperBase.__init__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___WrapperBase___init__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._WrapperBase.__init__"
  , params := ["obj", "method", "cache", "key", "lock", "cond"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["obj", "method", "cache", "key"], isMethod := some true, defaults := [("lock", (.lit .unit)), ("cond", (.lit .unit))] }
  , body := (.seq
            (.ifte
              (.call "isinstance" [(.name "obj"), (.name "type")])
              (.expr
                (.callValue
                  (.field (.name "<module>cachetools/_cachedmethod.py") "_warn_classmethod")
                  [(.kwargE "stacklevel" (.lit (.int 5)))]))
              .skip)
            (.seq
              (.expr
                (.mcall
                  (.field (.name "<module>cachetools/_cachedmethod.py") "functools")
                  "update_wrapper"
                  [(.name "self"), (.name "method")]))
              (.seq
                (.setField (.name "self") "_obj" (.name "obj"))
                (.seq
                  (.setField (.name "self") "_WrapperBase__cache" (.name "cache"))
                  (.seq
                    (.setField
                      (.name "self")
                      "_WrapperBase__key"
                      (.mcall
                        (.field (.name "<module>cachetools/_cachedmethod.py") "functools")
                        "partial"
                        [(.name "key"), (.name "obj")]))
                    (.seq
                      (.setField
                        (.name "self")
                        "_WrapperBase__lock"
                        (.cond
                          (.isOp true (.name "lock") (.lit .unit))
                          (.name "lock")
                          (.field (.name "<module>cachetools/_cachedmethod.py") "_none")))
                      (.seq
                        .skip
                        (.seq
                          (.setField
                            (.name "self")
                            "_WrapperBase__cond"
                            (.cond
                              (.isOp true (.name "cond") (.lit .unit))
                              (.name "cond")
                              (.field (.name "<module>cachetools/_cachedmethod.py") "_none")))
                          (.seq .skip (.seq .skip (.seq .skip .skip))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._WrapperBase.__call__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___WrapperBase___call__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._WrapperBase.__call__"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, receiverName := some "self" }
  , body := (.seq (.raise (.unop "py:exception:NotImplementedError" (.tupleE []))) .skip) }

/-- `cachetools/_cachedmethod.py:<module>._WrapperBase.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___WrapperBase_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._WrapperBase.cache_clear"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq (.raise (.unop "py:exception:NotImplementedError" (.tupleE []))) .skip) }

/-- `cachetools/_cachedmethod.py:<module>._WrapperBase.cache`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___WrapperBase_cache : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._WrapperBase.cache"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.ret (.mcall (.name "self") "_WrapperBase__cache" [(.field (.name "self") "_obj")])) }

/-- `cachetools/_cachedmethod.py:<module>._WrapperBase.cache_key`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___WrapperBase_cache_key : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._WrapperBase.cache_key"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.ret (.field (.name "self") "_WrapperBase__key")) }

/-- `cachetools/_cachedmethod.py:<module>._WrapperBase.cache_lock`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___WrapperBase_cache_lock : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._WrapperBase.cache_lock"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.ret (.mcall (.name "self") "_WrapperBase__lock" [(.field (.name "self") "_obj")])) }

/-- `cachetools/_cachedmethod.py:<module>._WrapperBase.cache_condition`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___WrapperBase_cache_condition : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._WrapperBase.cache_condition"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.ret (.mcall (.name "self") "_WrapperBase__cond" [(.field (.name "self") "_obj")])) }

/-- `cachetools/_cachedmethod.py:<module>._DescriptorBase.__init__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___DescriptorBase___init__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._DescriptorBase.__init__"
  , params := ["deprecated"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, defaults := [("deprecated", (.lit (.bool false)))] }
  , body := (.seq
            (.setField (.name "self") "_DescriptorBase__attrname" (.lit .unit))
            (.setField (.name "self") "_DescriptorBase__deprecated" (.name "deprecated"))) }

/-- `cachetools/_cachedmethod.py:<module>._DescriptorBase.__set_name__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___DescriptorBase___set_name__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._DescriptorBase.__set_name__"
  , params := ["owner", "name"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["owner", "name"], isMethod := some true }
  , body := (.seq
            (.ifte
              (.isOp false (.field (.name "self") "_DescriptorBase__attrname") (.lit .unit))
              (.setField (.name "self") "_DescriptorBase__attrname" (.name "name"))
              (.ifte
                (.binop "!=" (.name "name") (.field (.name "self") "_DescriptorBase__attrname"))
                (.raise
                  (.unop
                    "py:exception:TypeError"
                    (.tupleE
                      [ (.binop
                          "+"
                          (.lit
                            (.str "Cannot assign the same @cachedmethod to two different names "))
                          (.binop
                            "+"
                            (.binop
                              "+"
                              (.binop
                                "+"
                                (.binop
                                  "+"
                                  (.lit (.str "("))
                                  (.call
                                    "repr"
                                    [(.field (.name "self") "_DescriptorBase__attrname")]))
                                (.lit (.str " and ")))
                              (.call "repr" [(.name "name")]))
                            (.lit (.str ").")))) ])))
                .skip))
            .skip) }

/-- `cachetools/_cachedmethod.py:<module>._DescriptorBase.__get__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___DescriptorBase___get__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._DescriptorBase.__get__"
  , params := ["obj", "objtype"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["obj"], isMethod := some true, defaults := [("objtype", (.lit .unit))] }
  , body := (.seq
            (.assign "wrapper" (.mcall (.name "self") "Wrapper" [(.name "obj")]))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.isOp false (.name "obj") (.lit .unit))
                  .skip
                  (.ifte
                    (.isOp true (.field (.name "self") "_DescriptorBase__attrname") (.lit .unit))
                    (.tryCatch
                      (.seq
                        (.assign "tmp0" (.field (.name "obj") "__dict__"))
                        (.assign
                          "wrapper"
                          (.mcall
                            (.name "tmp0")
                            "setdefault"
                            [(.field (.name "self") "_DescriptorBase__attrname"), (.name "wrapper")])))
                      "$exprV$225"
                      (.ifte
                        (.inOp
                          false
                          (.name "$exprV$225")
                          (.tupleE [(.lit (.str "AttributeError"))]))
                        (.seq
                          (.assign
                            "msg"
                            (.binop
                              "+"
                              (.binop
                                "+"
                                (.binop
                                  "+"
                                  (.lit (.str "No '__dict__' attribute on "))
                                  (.call
                                    "repr"
                                    [(.field (.call "type" [(.name "obj")]) "__name__")]))
                                (.lit (.str " ")))
                              (.binop
                                "+"
                                (.binop
                                  "+"
                                  (.lit (.str "instance to cache "))
                                  (.call
                                    "repr"
                                    [(.field (.name "self") "_DescriptorBase__attrname")]))
                                (.lit (.str " property.")))))
                          (.ifte
                            (.field (.name "self") "_DescriptorBase__deprecated")
                            (.expr
                              (.callValue
                                (.field
                                  (.name "<module>cachetools/_cachedmethod.py")
                                  "_warn_instance_dict")
                                [(.name "msg"), (.lit (.int 3))]))
                            (.raise (.unop "py:exception:TypeError" (.tupleE [(.name "msg")])))))
                        (.ifte
                          (.inOp false (.name "$exprV$225") (.tupleE [(.lit (.str "TypeError"))]))
                          (.seq
                            (.assign
                              "msg"
                              (.binop
                                "+"
                                (.binop
                                  "+"
                                  (.binop
                                    "+"
                                    (.binop
                                      "+"
                                      (.lit (.str "The '__dict__' attribute on "))
                                      (.call
                                        "repr"
                                        [(.field (.call "type" [(.name "obj")]) "__name__")]))
                                    (.lit (.str " ")))
                                  (.lit (.str "instance does not support item assignment for ")))
                                (.binop
                                  "+"
                                  (.binop
                                    "+"
                                    (.lit (.str "caching "))
                                    (.call
                                      "repr"
                                      [(.field (.name "self") "_DescriptorBase__attrname")]))
                                  (.lit (.str " property.")))))
                            (.ifte
                              (.field (.name "self") "_DescriptorBase__deprecated")
                              (.expr
                                (.callValue
                                  (.field
                                    (.name "<module>cachetools/_cachedmethod.py")
                                    "_warn_instance_dict")
                                  [(.name "msg"), (.lit (.int 3))]))
                              (.raise (.unop "py:exception:TypeError" (.tupleE [(.name "msg")])))))
                          (.raise (.name "$exprV$225")))))
                    (.ifte
                      (.field (.name "self") "_DescriptorBase__deprecated")
                      .skip
                      (.seq
                        (.assign
                          "msg"
                          (.lit
                            (.str "Cannot use @cachedmethod instance without calling __set_name__ on it")))
                        (.raise (.unop "py:exception:TypeError" (.tupleE [(.name "msg")])))))))
                (.seq
                  .skip
                  (.seq (.ret (.name "wrapper")) (.seq .skip (.seq .skip (.seq .skip .skip)))))))) }

/-- `cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase.__init__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___DeprecatedDescriptorBase___init__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase.__init__"
  , params := ["wrapper", "cache_clear"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["wrapper", "cache_clear"], isMethod := some true }
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "super" []))
              (.expr
                (.mcall (.name "tmp0") "__init__" [(.kwargE "deprecated" (.lit (.bool true)))])))
            (.seq
              (.setField (.name "self") "_DeprecatedDescriptorBase__wrapper" (.name "wrapper"))
              (.seq
                (.setField
                  (.name "self")
                  "_DeprecatedDescriptorBase__cache_clear"
                  (.name "cache_clear"))
                (.seq .skip .skip)))) }

/-- `cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase.__call__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___DeprecatedDescriptorBase___call__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase.__call__"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, receiverName := some "self" }
  , body := (.seq
            (.expr
              (.callValue
                (.field (.name "<module>cachetools/_cachedmethod.py") "_warn_classmethod")
                [(.kwargE "stacklevel" (.lit (.int 3)))]))
            (.seq
              .skip
              (.ret
                (.mcall
                  (.name "self")
                  "_DeprecatedDescriptorBase__wrapper"
                  [(.starred (.name "args")), (.dstarred (.name "kwargs"))])))) }

/-- `cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___DeprecatedDescriptorBase_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase.cache_clear"
  , params := ["objtype"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["objtype"], isMethod := some true }
  , body := (.seq
            (.expr
              (.callValue
                (.field (.name "<module>cachetools/_cachedmethod.py") "_warn_classmethod")
                [(.kwargE "stacklevel" (.lit (.int 3)))]))
            (.seq
              .skip
              (.ret
                (.mcall (.name "self") "_DeprecatedDescriptorBase__cache_clear" [(.name "objtype")])))) }

/-- `cachetools/_cachedmethod.py:<module>._condition_info`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_info : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition_info"
  , params := ["method", "cache", "key", "lock", "cond", "info"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["method", "cache", "key", "lock", "cond", "info"], isMethod := some false }
  , body := (.seq
            (.seq
              (.assign
                "Descriptor"
                (.classClosure
                  "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor<meta>"))
              (.expr
                (.classClosure
                  "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor<meta>")))
            (.seq
              (.ret (.alloc "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor" []))
              (.seq .skip (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.__init__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper___init__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.__init__"
  , params := ["obj"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["obj"], isMethod := some true }
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "super" []))
              (.expr
                (.mcall
                  (.name "tmp0")
                  "__init__"
                  [ (.name "obj")
                  , (.name "method")
                  , (.name "cache")
                  , (.name "key")
                  , (.name "lock")
                  , (.name "cond") ])))
            (.seq
              (.seq
                (.assign "tmp1" (.lit (.int 0)))
                (.seq
                  (.setField (.name "self") "_Wrapper__hits" (.name "tmp1"))
                  (.setField (.name "self") "_Wrapper__misses" (.name "tmp1"))))
              (.seq
                (.setField (.name "self") "_Wrapper__pending" (.call "set" []))
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.__call__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper___call__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.__call__"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, receiverName := some "self" }
  , body := (.seq
            (.assign "cache" (.field (.name "self") "cache"))
            (.seq
              (.assign "lock" (.field (.name "self") "cache_lock"))
              (.seq
                (.assign "cond" (.field (.name "self") "cache_condition"))
                (.seq
                  (.assign
                    "key"
                    (.mcall
                      (.name "self")
                      "cache_key"
                      [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                  (.seq
                    (.seq
                      (.assign "manager_tmp0" (.name "lock"))
                      (.seq
                        (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                        (.seq
                          (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                          (.seq
                            (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                            (.tryFinally
                              (.seq
                                (.expr
                                  (.mcall
                                    (.name "cond")
                                    "wait_for"
                                    [ (.closure
                                        "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.__call__.<lambda>0") ]))
                                (.tryCatch
                                  (.seq
                                    (.assign "result" (.index (.name "cache") (.name "key")))
                                    (.seq
                                      (.setField
                                        (.name "self")
                                        "_Wrapper__hits"
                                        (.binop
                                        "+"
                                        (.field (.name "self") "_Wrapper__hits")
                                        (.lit (.int 1))))
                                      (.ret (.name "result"))))
                                  "$exprV$226"
                                  (.ifte
                                    (.inOp
                                      false
                                      (.name "$exprV$226")
                                      (.tupleE [(.lit (.str "KeyError"))]))
                                    (.seq
                                      (.seq
                                        (.assign "tmp0" (.field (.name "self") "_Wrapper__pending"))
                                        (.expr (.mcall (.name "tmp0") "add" [(.name "key")])))
                                      (.setField
                                        (.name "self")
                                        "_Wrapper__misses"
                                        (.binop
                                        "+"
                                        (.field (.name "self") "_Wrapper__misses")
                                        (.lit (.int 1)))))
                                    (.raise (.name "$exprV$226")))))
                              (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                    (.seq
                      (.tryFinally
                        (.seq
                          (.assign
                            "val"
                            (.callValue
                              (.name "method")
                              [ (.field (.name "self") "_obj")
                              , (.starred (.name "args"))
                              , (.dstarred (.name "kwargs")) ]))
                          (.seq
                            (.assign "manager_tmp1" (.name "lock"))
                            (.seq
                              (.assign "enter_tmp1" (.field (.name "manager_tmp1") "__enter__"))
                              (.seq
                                (.assign "exit_tmp1" (.field (.name "manager_tmp1") "__exit__"))
                                (.seq
                                  (.assign
                                    "value_tmp1"
                                    (.mcall (.name "manager_tmp1") "__enter__" []))
                                  (.tryFinally
                                    (.seq
                                      (.tryCatch
                                        (.setIndex (.name "cache") (.name "key") (.name "val"))
                                        "$exprV$227"
                                        (.ifte
                                        (.inOp
                                        false
                                        (.name "$exprV$227")
                                        (.tupleE [(.lit (.str "ValueError"))]))
                                        .skip
                                        (.raise (.name "$exprV$227"))))
                                      (.ret (.name "val")))
                                    (.expr (.mcall (.name "manager_tmp1") "__exit__" []))))))))
                        (.seq
                          (.assign "manager_tmp2" (.name "lock"))
                          (.seq
                            (.assign "enter_tmp2" (.field (.name "manager_tmp2") "__enter__"))
                            (.seq
                              (.assign "exit_tmp2" (.field (.name "manager_tmp2") "__exit__"))
                              (.seq
                                (.assign
                                  "value_tmp2"
                                  (.mcall (.name "manager_tmp2") "__enter__" []))
                                (.tryFinally
                                  (.seq
                                    (.seq
                                      (.assign "tmp1" (.field (.name "self") "_Wrapper__pending"))
                                      (.expr (.mcall (.name "tmp1") "remove" [(.name "key")])))
                                    (.expr (.mcall (.name "cond") "notify_all" [])))
                                  (.expr (.mcall (.name "manager_tmp2") "__exit__" []))))))))
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))))))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.__call__.<lambda>0`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper___call____lambda_0 : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.__call__.<lambda>0"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            (.ret (.inOp true (.name "key") (.field (.name "self") "_Wrapper__pending")))
            (.seq .skip .skip)) }

/-- `cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.cache_clear"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "cache_lock"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.seq
                        (.seq
                          (.assign "tmp0" (.field (.name "self") "cache"))
                          (.expr (.mcall (.name "tmp0") "clear" [])))
                        (.seq
                          (.assign "tmp1" (.lit (.int 0)))
                          (.seq
                            (.setField (.name "self") "_Wrapper__hits" (.name "tmp1"))
                            (.setField (.name "self") "_Wrapper__misses" (.name "tmp1")))))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))) }

/-- `cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.cache_info`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper_cache_info : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.cache_info"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "cache_lock"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.ret
                        (.callValue
                          (.name "info")
                          [ (.field (.name "self") "cache")
                          , (.field (.name "self") "_Wrapper__hits")
                          , (.field (.name "self") "_Wrapper__misses") ]))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/_cachedmethod.py:<module>._locked_info`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_info : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked_info"
  , params := ["method", "cache", "key", "lock", "info"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["method", "cache", "key", "lock", "info"], isMethod := some false }
  , body := (.seq
            (.seq
              (.assign
                "Descriptor"
                (.classClosure "cachetools/_cachedmethod.py:<module>._locked_info.Descriptor<meta>"))
              (.expr
                (.classClosure "cachetools/_cachedmethod.py:<module>._locked_info.Descriptor<meta>")))
            (.seq
              (.ret (.alloc "cachetools/_cachedmethod.py:<module>._locked_info.Descriptor" []))
              (.seq .skip (.seq .skip .skip)))) }

/-- `cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.__init__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_info_Descriptor_Wrapper___init__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.__init__"
  , params := ["obj"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["obj"], isMethod := some true }
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "super" []))
              (.expr
                (.mcall
                  (.name "tmp0")
                  "__init__"
                  [(.name "obj"), (.name "method"), (.name "cache"), (.name "key"), (.name "lock")])))
            (.seq
              (.seq
                (.assign "tmp1" (.lit (.int 0)))
                (.seq
                  (.setField (.name "self") "_Wrapper__hits" (.name "tmp1"))
                  (.setField (.name "self") "_Wrapper__misses" (.name "tmp1"))))
              (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))) }

/-- `cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.__call__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_info_Descriptor_Wrapper___call__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.__call__"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, receiverName := some "self" }
  , body := (.seq
            (.assign "cache" (.field (.name "self") "cache"))
            (.seq
              (.assign "lock" (.field (.name "self") "cache_lock"))
              (.seq
                (.assign
                  "key"
                  (.mcall
                    (.name "self")
                    "cache_key"
                    [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                (.seq
                  (.seq
                    (.assign "manager_tmp0" (.name "lock"))
                    (.seq
                      (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                      (.seq
                        (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                        (.seq
                          (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                          (.tryFinally
                            (.tryCatch
                              (.seq
                                (.assign "result" (.index (.name "cache") (.name "key")))
                                (.seq
                                  (.setField
                                    (.name "self")
                                    "_Wrapper__hits"
                                    (.binop
                                      "+"
                                      (.field (.name "self") "_Wrapper__hits")
                                      (.lit (.int 1))))
                                  (.ret (.name "result"))))
                              "$exprV$228"
                              (.ifte
                                (.inOp
                                  false
                                  (.name "$exprV$228")
                                  (.tupleE [(.lit (.str "KeyError"))]))
                                (.setField
                                  (.name "self")
                                  "_Wrapper__misses"
                                  (.binop
                                    "+"
                                    (.field (.name "self") "_Wrapper__misses")
                                    (.lit (.int 1))))
                                (.raise (.name "$exprV$228"))))
                            (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "val"
                        (.callValue
                          (.name "method")
                          [ (.field (.name "self") "_obj")
                          , (.starred (.name "args"))
                          , (.dstarred (.name "kwargs")) ]))
                      (.seq
                        .skip
                        (.seq
                          (.seq
                            (.assign "manager_tmp1" (.name "lock"))
                            (.seq
                              (.assign "enter_tmp1" (.field (.name "manager_tmp1") "__enter__"))
                              (.seq
                                (.assign "exit_tmp1" (.field (.name "manager_tmp1") "__exit__"))
                                (.seq
                                  (.assign
                                    "value_tmp1"
                                    (.mcall (.name "manager_tmp1") "__enter__" []))
                                  (.tryFinally
                                    (.tryCatch
                                      (.ret
                                        (.mcall
                                        (.name "cache")
                                        "setdefault"
                                        [ (.fnref
                                        "cachetools/_cachedmethod.py:<module>._WrapperBase.cache")
                                        , (.name "key")
                                        , (.name "val") ]))
                                      "$exprV$229"
                                      (.ifte
                                        (.inOp
                                        false
                                        (.name "$exprV$229")
                                        (.tupleE [(.lit (.str "ValueError"))]))
                                        (.ret (.name "val"))
                                        (.raise (.name "$exprV$229"))))
                                    (.expr (.mcall (.name "manager_tmp1") "__exit__" [])))))))
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_info_Descriptor_Wrapper_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.cache_clear"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "cache_lock"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.seq
                        (.seq
                          (.assign "tmp0" (.field (.name "self") "cache"))
                          (.expr (.mcall (.name "tmp0") "clear" [])))
                        (.seq
                          (.assign "tmp1" (.lit (.int 0)))
                          (.seq
                            (.setField (.name "self") "_Wrapper__hits" (.name "tmp1"))
                            (.setField (.name "self") "_Wrapper__misses" (.name "tmp1")))))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))) }

/-- `cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.cache_info`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_info_Descriptor_Wrapper_cache_info : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.cache_info"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "cache_lock"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.ret
                        (.callValue
                          (.name "info")
                          [ (.field (.name "self") "cache")
                          , (.field (.name "self") "_Wrapper__hits")
                          , (.field (.name "self") "_Wrapper__misses") ]))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked_info`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_info : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked_info"
  , params := ["method", "cache", "key", "info"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["method", "cache", "key", "info"], isMethod := some false }
  , body := (.seq
            (.seq
              (.assign
                "Descriptor"
                (.classClosure
                  "cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor<meta>"))
              (.expr
                (.classClosure
                  "cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor<meta>")))
            (.seq
              (.ret (.alloc "cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor" []))
              (.seq .skip .skip))) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.__init__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_info_Descriptor_Wrapper___init__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.__init__"
  , params := ["obj"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["obj"], isMethod := some true }
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "super" []))
              (.expr
                (.mcall
                  (.name "tmp0")
                  "__init__"
                  [(.name "obj"), (.name "method"), (.name "cache"), (.name "key")])))
            (.seq
              (.seq
                (.assign "tmp1" (.lit (.int 0)))
                (.seq
                  (.setField (.name "self") "_Wrapper__hits" (.name "tmp1"))
                  (.setField (.name "self") "_Wrapper__misses" (.name "tmp1"))))
              (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.__call__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_info_Descriptor_Wrapper___call__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.__call__"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, receiverName := some "self" }
  , body := (.seq
            (.assign "cache" (.field (.name "self") "cache"))
            (.seq
              (.assign
                "key"
                (.mcall
                  (.name "self")
                  "cache_key"
                  [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
              (.seq
                (.tryCatch
                  (.seq
                    (.assign "result" (.index (.name "cache") (.name "key")))
                    (.seq
                      (.setField
                        (.name "self")
                        "_Wrapper__hits"
                        (.binop "+" (.field (.name "self") "_Wrapper__hits") (.lit (.int 1))))
                      (.ret (.name "result"))))
                  "$exprV$230"
                  (.ifte
                    (.inOp false (.name "$exprV$230") (.tupleE [(.lit (.str "KeyError"))]))
                    (.setField
                      (.name "self")
                      "_Wrapper__misses"
                      (.binop "+" (.field (.name "self") "_Wrapper__misses") (.lit (.int 1))))
                    (.raise (.name "$exprV$230"))))
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "val"
                      (.callValue
                        (.name "method")
                        [ (.field (.name "self") "_obj")
                        , (.starred (.name "args"))
                        , (.dstarred (.name "kwargs")) ]))
                    (.seq
                      .skip
                      (.seq
                        (.tryCatch
                          (.setIndex (.name "cache") (.name "key") (.name "val"))
                          "$exprV$231"
                          (.ifte
                            (.inOp
                              false
                              (.name "$exprV$231")
                              (.tupleE [(.lit (.str "ValueError"))]))
                            .skip
                            (.raise (.name "$exprV$231"))))
                        (.seq .skip (.seq (.ret (.name "val")) (.seq .skip .skip)))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_info_Descriptor_Wrapper_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.cache_clear"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.seq
              (.assign "tmp0" (.field (.name "self") "cache"))
              (.expr (.mcall (.name "tmp0") "clear" [])))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp1" (.lit (.int 0)))
                  (.seq
                    (.setField (.name "self") "_Wrapper__hits" (.name "tmp1"))
                    (.setField (.name "self") "_Wrapper__misses" (.name "tmp1"))))
                .skip))) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.cache_info`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_info_Descriptor_Wrapper_cache_info : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.cache_info"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq
            (.ret
              (.callValue
                (.name "info")
                [ (.field (.name "self") "cache")
                , (.field (.name "self") "_Wrapper__hits")
                , (.field (.name "self") "_Wrapper__misses") ]))
            .skip) }

/-- `cachetools/_cachedmethod.py:<module>._condition`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition"
  , params := ["method", "cache", "key", "lock", "cond"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["method", "cache", "key", "lock", "cond"], isMethod := some false }
  , body := (.seq
            (.assign
              "pending"
              (.hole "class-construction:unresolved-lexical-identity:WeakKeyDictionary"))
            (.seq
              (.assign
                "wrapper"
                (.closure "cachetools/_cachedmethod.py:<module>._condition.wrapper"))
              (.seq
                (.assign
                  "cache_clear"
                  (.closure "cachetools/_cachedmethod.py:<module>._condition.cache_clear"))
                (.seq
                  (.assign
                    "classmethod_wrapper"
                    (.closure "cachetools/_cachedmethod.py:<module>._condition.classmethod_wrapper"))
                  (.seq
                    (.seq
                      (.assign
                        "Descriptor"
                        (.classClosure
                          "cachetools/_cachedmethod.py:<module>._condition.Descriptor<meta>"))
                      (.expr
                        (.classClosure
                          "cachetools/_cachedmethod.py:<module>._condition.Descriptor<meta>")))
                    (.seq
                      (.ret
                        (.alloc
                          "cachetools/_cachedmethod.py:<module>._condition.Descriptor"
                          [(.name "classmethod_wrapper"), (.name "cache_clear")]))
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._condition.wrapper`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_wrapper : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition.wrapper"
  , params := ["self", "pending", "args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["self", "pending"], isMethod := some false }
  , body := (.seq
            (.assign "c" (.callValue (.name "cache") [(.name "self")]))
            (.seq
              (.assign
                "k"
                (.callValue
                  (.name "key")
                  [(.name "self"), (.starred (.name "args")), (.dstarred (.name "kwargs"))]))
              (.seq
                (.seq
                  (.assign "manager_tmp0" (.callValue (.name "lock") [(.name "self")]))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.seq
                            (.seq
                              (.assign "tmp0" (.callValue (.name "cond") [(.name "self")]))
                              (.expr
                                (.mcall
                                  (.name "tmp0")
                                  "wait_for"
                                  [ (.closure
                                      "cachetools/_cachedmethod.py:<module>._condition.wrapper.<lambda>1") ])))
                            (.tryCatch
                              (.ret (.index (.name "c") (.name "k")))
                              "$exprV$232"
                              (.ifte
                                (.inOp
                                  false
                                  (.name "$exprV$232")
                                  (.tupleE [(.lit (.str "KeyError"))]))
                                (.expr (.mcall (.name "pending") "add" [(.name "k")]))
                                (.raise (.name "$exprV$232")))))
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                (.seq
                  .skip
                  (.seq
                    (.tryFinally
                      (.seq
                        (.assign
                          "v"
                          (.callValue
                            (.name "method")
                            [ (.name "self")
                            , (.starred (.name "args"))
                            , (.dstarred (.name "kwargs")) ]))
                        (.seq
                          (.assign "manager_tmp1" (.callValue (.name "lock") [(.name "self")]))
                          (.seq
                            (.assign "enter_tmp1" (.field (.name "manager_tmp1") "__enter__"))
                            (.seq
                              (.assign "exit_tmp1" (.field (.name "manager_tmp1") "__exit__"))
                              (.seq
                                (.assign
                                  "value_tmp1"
                                  (.mcall (.name "manager_tmp1") "__enter__" []))
                                (.tryFinally
                                  (.seq
                                    (.tryCatch
                                      (.setIndex (.name "c") (.name "k") (.name "v"))
                                      "$exprV$233"
                                      (.ifte
                                        (.inOp
                                        false
                                        (.name "$exprV$233")
                                        (.tupleE [(.lit (.str "ValueError"))]))
                                        .skip
                                        (.raise (.name "$exprV$233"))))
                                    (.ret (.name "v")))
                                  (.expr (.mcall (.name "manager_tmp1") "__exit__" []))))))))
                      (.seq
                        (.assign "manager_tmp2" (.callValue (.name "lock") [(.name "self")]))
                        (.seq
                          (.assign "enter_tmp2" (.field (.name "manager_tmp2") "__enter__"))
                          (.seq
                            (.assign "exit_tmp2" (.field (.name "manager_tmp2") "__exit__"))
                            (.seq
                              (.assign "value_tmp2" (.mcall (.name "manager_tmp2") "__enter__" []))
                              (.tryFinally
                                (.seq
                                  (.expr (.mcall (.name "pending") "remove" [(.name "k")]))
                                  (.seq
                                    (.assign "tmp1" (.callValue (.name "cond") [(.name "self")]))
                                    (.expr (.mcall (.name "tmp1") "notify_all" []))))
                                (.expr (.mcall (.name "manager_tmp2") "__exit__" []))))))))
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._condition.wrapper.<lambda>1`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_wrapper__lambda_1 : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition.wrapper.<lambda>1"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq (.ret (.inOp true (.name "k") (.name "pending"))) (.seq .skip .skip)) }

/-- `cachetools/_cachedmethod.py:<module>._condition.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition.cache_clear"
  , params := ["self"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["self"], isMethod := some false }
  , body := (.seq
            (.assign "c" (.callValue (.name "cache") [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "manager_tmp0" (.callValue (.name "lock") [(.name "self")]))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.expr (.mcall (.name "c") "clear" []))
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._condition.classmethod_wrapper`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_classmethod_wrapper : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition.classmethod_wrapper"
  , params := ["self", "args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["self"], isMethod := some false }
  , body := (.seq
            (.assign "p" (.mcall (.name "pending") "setdefault" [(.name "self"), (.call "set" [])]))
            (.seq
              .skip
              (.seq
                (.ret
                  (.callValue
                    (.name "wrapper")
                    [ (.name "self")
                    , (.name "p")
                    , (.starred (.name "args"))
                    , (.dstarred (.name "kwargs")) ]))
                (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/_cachedmethod.py:<module>._condition.Descriptor.Wrapper.__init__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_Descriptor_Wrapper___init__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition.Descriptor.Wrapper.__init__"
  , params := ["obj"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["obj"], isMethod := some true }
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "super" []))
              (.expr
                (.mcall
                  (.name "tmp0")
                  "__init__"
                  [ (.name "obj")
                  , (.name "method")
                  , (.name "cache")
                  , (.name "key")
                  , (.name "lock")
                  , (.name "cond") ])))
            (.seq
              (.setField (.name "self") "_Wrapper__pending" (.call "set" []))
              (.seq
                .skip
                (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._condition.Descriptor.Wrapper.__call__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_Descriptor_Wrapper___call__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition.Descriptor.Wrapper.__call__"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, receiverName := some "self" }
  , body := (.seq
            (.ret
              (.callValue
                (.name "wrapper")
                [ (.field (.name "self") "_obj")
                , (.field (.name "self") "_Wrapper__pending")
                , (.starred (.name "args"))
                , (.dstarred (.name "kwargs")) ]))
            .skip) }

/-- `cachetools/_cachedmethod.py:<module>._condition.Descriptor.Wrapper.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_Descriptor_Wrapper_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition.Descriptor.Wrapper.cache_clear"
  , params := ["_objtype"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, defaults := [("_objtype", (.lit .unit))] }
  , body := (.seq (.ret (.callValue (.name "cache_clear") [(.field (.name "self") "_obj")])) .skip) }

/-- `cachetools/_cachedmethod.py:<module>._locked`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked"
  , params := ["method", "cache", "key", "lock"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["method", "cache", "key", "lock"], isMethod := some false }
  , body := (.seq
            (.assign "wrapper" (.closure "cachetools/_cachedmethod.py:<module>._locked.wrapper"))
            (.seq
              (.assign
                "cache_clear"
                (.closure "cachetools/_cachedmethod.py:<module>._locked.cache_clear"))
              (.seq
                (.seq
                  (.assign
                    "Descriptor"
                    (.classClosure "cachetools/_cachedmethod.py:<module>._locked.Descriptor<meta>"))
                  (.expr
                    (.classClosure "cachetools/_cachedmethod.py:<module>._locked.Descriptor<meta>")))
                (.seq
                  (.ret
                    (.alloc
                      "cachetools/_cachedmethod.py:<module>._locked.Descriptor"
                      [(.name "wrapper"), (.name "cache_clear")]))
                  (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))) }

/-- `cachetools/_cachedmethod.py:<module>._locked.wrapper`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_wrapper : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked.wrapper"
  , params := ["self", "args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["self"], isMethod := some false }
  , body := (.seq
            (.assign "c" (.callValue (.name "cache") [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.assign
                  "k"
                  (.callValue
                    (.name "key")
                    [(.name "self"), (.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                (.seq
                  .skip
                  (.seq
                    (.seq
                      (.assign "manager_tmp0" (.callValue (.name "lock") [(.name "self")]))
                      (.seq
                        (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                        (.seq
                          (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                          (.seq
                            (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                            (.tryFinally
                              (.tryCatch
                                (.ret (.index (.name "c") (.name "k")))
                                "$exprV$234"
                                (.ifte
                                  (.inOp
                                    false
                                    (.name "$exprV$234")
                                    (.tupleE [(.lit (.str "KeyError"))]))
                                  .skip
                                  (.raise (.name "$exprV$234"))))
                              (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "v"
                          (.callValue
                            (.name "method")
                            [ (.name "self")
                            , (.starred (.name "args"))
                            , (.dstarred (.name "kwargs")) ]))
                        (.seq
                          .skip
                          (.seq
                            (.seq
                              (.assign "manager_tmp1" (.callValue (.name "lock") [(.name "self")]))
                              (.seq
                                (.assign "enter_tmp1" (.field (.name "manager_tmp1") "__enter__"))
                                (.seq
                                  (.assign "exit_tmp1" (.field (.name "manager_tmp1") "__exit__"))
                                  (.seq
                                    (.assign
                                      "value_tmp1"
                                      (.mcall (.name "manager_tmp1") "__enter__" []))
                                    (.tryFinally
                                      (.tryCatch
                                        (.ret
                                        (.mcall (.name "c") "setdefault" [(.name "k"), (.name "v")]))
                                        "$exprV$235"
                                        (.ifte
                                        (.inOp
                                        false
                                        (.name "$exprV$235")
                                        (.tupleE [(.lit (.str "ValueError"))]))
                                        (.ret (.name "v"))
                                        (.raise (.name "$exprV$235"))))
                                      (.expr (.mcall (.name "manager_tmp1") "__exit__" [])))))))
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._locked.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked.cache_clear"
  , params := ["self"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["self"], isMethod := some false }
  , body := (.seq
            (.assign "c" (.callValue (.name "cache") [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "manager_tmp0" (.callValue (.name "lock") [(.name "self")]))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.expr (.mcall (.name "c") "clear" []))
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._locked.Descriptor.Wrapper.__init__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_Descriptor_Wrapper___init__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked.Descriptor.Wrapper.__init__"
  , params := ["obj"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["obj"], isMethod := some true }
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "super" []))
              (.expr
                (.mcall
                  (.name "tmp0")
                  "__init__"
                  [(.name "obj"), (.name "method"), (.name "cache"), (.name "key"), (.name "lock")])))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/_cachedmethod.py:<module>._locked.Descriptor.Wrapper.__call__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_Descriptor_Wrapper___call__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked.Descriptor.Wrapper.__call__"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, receiverName := some "self" }
  , body := (.seq
            (.ret
              (.callValue
                (.name "wrapper")
                [ (.field (.name "self") "_obj")
                , (.starred (.name "args"))
                , (.dstarred (.name "kwargs")) ]))
            .skip) }

/-- `cachetools/_cachedmethod.py:<module>._locked.Descriptor.Wrapper.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_Descriptor_Wrapper_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked.Descriptor.Wrapper.cache_clear"
  , params := ["_objtype"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, defaults := [("_objtype", (.lit .unit))] }
  , body := (.seq (.ret (.callValue (.name "cache_clear") [(.field (.name "self") "_obj")])) .skip) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked"
  , params := ["method", "cache", "key"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["method", "cache", "key"], isMethod := some false }
  , body := (.seq
            (.assign "wrapper" (.closure "cachetools/_cachedmethod.py:<module>._unlocked.wrapper"))
            (.seq
              (.assign
                "cache_clear"
                (.closure "cachetools/_cachedmethod.py:<module>._unlocked.cache_clear"))
              (.seq
                (.seq
                  (.assign
                    "Descriptor"
                    (.classClosure
                      "cachetools/_cachedmethod.py:<module>._unlocked.Descriptor<meta>"))
                  (.expr
                    (.classClosure
                      "cachetools/_cachedmethod.py:<module>._unlocked.Descriptor<meta>")))
                (.seq
                  (.ret
                    (.alloc
                      "cachetools/_cachedmethod.py:<module>._unlocked.Descriptor"
                      [(.name "wrapper"), (.name "cache_clear")]))
                  (.seq .skip (.seq .skip (.seq .skip .skip))))))) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked.wrapper`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_wrapper : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked.wrapper"
  , params := ["self", "args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["self"], isMethod := some false }
  , body := (.seq
            (.assign "c" (.callValue (.name "cache") [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.assign
                  "k"
                  (.callValue
                    (.name "key")
                    [(.name "self"), (.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                (.seq
                  .skip
                  (.seq
                    (.tryCatch
                      (.ret (.index (.name "c") (.name "k")))
                      "$exprV$236"
                      (.ifte
                        (.inOp false (.name "$exprV$236") (.tupleE [(.lit (.str "KeyError"))]))
                        .skip
                        (.raise (.name "$exprV$236"))))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "v"
                          (.callValue
                            (.name "method")
                            [ (.name "self")
                            , (.starred (.name "args"))
                            , (.dstarred (.name "kwargs")) ]))
                        (.seq
                          .skip
                          (.seq
                            (.tryCatch
                              (.setIndex (.name "c") (.name "k") (.name "v"))
                              "$exprV$237"
                              (.ifte
                                (.inOp
                                  false
                                  (.name "$exprV$237")
                                  (.tupleE [(.lit (.str "ValueError"))]))
                                .skip
                                (.raise (.name "$exprV$237"))))
                            (.seq .skip (.seq (.ret (.name "v")) .skip))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked.cache_clear"
  , params := ["self"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["self"], isMethod := some false }
  , body := (.seq
            (.assign "c" (.callValue (.name "cache") [(.name "self")]))
            (.seq .skip (.seq (.expr (.mcall (.name "c") "clear" [])) .skip))) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked.Descriptor.Wrapper.__init__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_Descriptor_Wrapper___init__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked.Descriptor.Wrapper.__init__"
  , params := ["obj"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["obj"], isMethod := some true }
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "super" []))
              (.expr
                (.mcall
                  (.name "tmp0")
                  "__init__"
                  [(.name "obj"), (.name "method"), (.name "cache"), (.name "key")])))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked.Descriptor.Wrapper.__call__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_Descriptor_Wrapper___call__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked.Descriptor.Wrapper.__call__"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, receiverName := some "self" }
  , body := (.seq
            (.ret
              (.callValue
                (.name "wrapper")
                [ (.field (.name "self") "_obj")
                , (.starred (.name "args"))
                , (.dstarred (.name "kwargs")) ]))
            .skip) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked.Descriptor.Wrapper.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_Descriptor_Wrapper_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked.Descriptor.Wrapper.cache_clear"
  , params := ["_objtype"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, defaults := [("_objtype", (.lit .unit))] }
  , body := (.seq (.ret (.callValue (.name "cache_clear") [(.field (.name "self") "_obj")])) .skip) }

/-- `cachetools/_cachedmethod.py:<module>._wrapper`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___wrapper : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._wrapper"
  , params := ["method", "cache", "key", "lock", "cond", "info"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["method", "cache", "key"], isMethod := some false, defaults := [("lock", (.lit .unit)), ("cond", (.lit .unit)), ("info", (.lit .unit))] }
  , body := (.seq
            (.ifte
              (.isOp true (.name "info") (.lit .unit))
              (.seq
                (.assign "$exprV$238" (.isOp true (.name "cond") (.lit .unit)))
                (.seq
                  (.ifte
                    (.name "$exprV$238")
                    (.seq
                      (.assign "$exprV$239" (.isOp true (.name "lock") (.lit .unit)))
                      (.assign "$exprV$240" (.lit (.int 0))))
                    (.seq
                      (.assign "$exprV$239" (.name "$exprV$238"))
                      (.assign "$exprV$240" (.lit (.int 1)))))
                  (.ifte
                    (.cond
                      (.binop "==" (.name "$exprV$240") (.lit (.int 0)))
                      (.cond (.name "$exprV$239") (.lit (.bool true)) (.lit (.bool false)))
                      (.binop "==" (.name "$exprV$240") (.lit (.int 2))))
                    (.assign
                      "wrapper"
                      (.callValue
                        (.field (.name "<module>cachetools/_cachedmethod.py") "_condition_info")
                        [ (.name "method")
                        , (.name "cache")
                        , (.name "key")
                        , (.name "lock")
                        , (.name "cond")
                        , (.name "info") ]))
                    (.ifte
                      (.isOp true (.name "cond") (.lit .unit))
                      (.assign
                        "wrapper"
                        (.callValue
                          (.field (.name "<module>cachetools/_cachedmethod.py") "_condition_info")
                          [ (.name "method")
                          , (.name "cache")
                          , (.name "key")
                          , (.name "cond")
                          , (.name "cond")
                          , (.name "info") ]))
                      (.ifte
                        (.isOp true (.name "lock") (.lit .unit))
                        (.assign
                          "wrapper"
                          (.callValue
                            (.field (.name "<module>cachetools/_cachedmethod.py") "_locked_info")
                            [ (.name "method")
                            , (.name "cache")
                            , (.name "key")
                            , (.name "lock")
                            , (.name "info") ]))
                        (.assign
                          "wrapper"
                          (.callValue
                            (.field (.name "<module>cachetools/_cachedmethod.py") "_unlocked_info")
                            [(.name "method"), (.name "cache"), (.name "key"), (.name "info")])))))))
              (.seq
                (.assign "$exprV$241" (.isOp true (.name "cond") (.lit .unit)))
                (.seq
                  (.ifte
                    (.name "$exprV$241")
                    (.seq
                      (.assign "$exprV$242" (.isOp true (.name "lock") (.lit .unit)))
                      (.assign "$exprV$243" (.lit (.int 0))))
                    (.seq
                      (.assign "$exprV$242" (.name "$exprV$241"))
                      (.assign "$exprV$243" (.lit (.int 1)))))
                  (.ifte
                    (.cond
                      (.binop "==" (.name "$exprV$243") (.lit (.int 0)))
                      (.cond (.name "$exprV$242") (.lit (.bool true)) (.lit (.bool false)))
                      (.binop "==" (.name "$exprV$243") (.lit (.int 2))))
                    (.assign
                      "wrapper"
                      (.callValue
                        (.field (.name "<module>cachetools/_cachedmethod.py") "_condition")
                        [ (.name "method")
                        , (.name "cache")
                        , (.name "key")
                        , (.name "lock")
                        , (.name "cond") ]))
                    (.ifte
                      (.isOp true (.name "cond") (.lit .unit))
                      (.assign
                        "wrapper"
                        (.callValue
                          (.field (.name "<module>cachetools/_cachedmethod.py") "_condition")
                          [ (.name "method")
                          , (.name "cache")
                          , (.name "key")
                          , (.name "cond")
                          , (.name "cond") ]))
                      (.ifte
                        (.isOp true (.name "lock") (.lit .unit))
                        (.assign
                          "wrapper"
                          (.callValue
                            (.field (.name "<module>cachetools/_cachedmethod.py") "_locked")
                            [(.name "method"), (.name "cache"), (.name "key"), (.name "lock")]))
                        (.assign
                          "wrapper"
                          (.callValue
                            (.field (.name "<module>cachetools/_cachedmethod.py") "_unlocked")
                            [(.name "method"), (.name "cache"), (.name "key")]))))))))
            (.seq
              .skip
              (.seq
                (.setField (.name "wrapper") "cache" (.name "cache"))
                (.seq
                  .skip
                  (.seq
                    (.setField (.name "wrapper") "cache_key" (.name "key"))
                    (.seq
                      .skip
                      (.seq
                        (.setField
                          (.name "wrapper")
                          "cache_lock"
                          (.cond
                            (.isOp true (.name "lock") (.lit .unit))
                            (.name "lock")
                            (.name "cond")))
                        (.seq
                          .skip
                          (.seq
                            (.setField (.name "wrapper") "cache_condition" (.name "cond"))
                            (.seq
                              .skip
                              (.seq
                                (.ret
                                  (.mcall
                                    (.field
                                      (.name "<module>cachetools/_cachedmethod.py")
                                      "functools")
                                    "update_wrapper"
                                    [(.name "wrapper"), (.name "method")]))
                                (.seq .skip (.seq .skip .skip))))))))))))) }

/-- `cachetools/func.py:<module>._UnboundTTLCache.__init__`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module___UnboundTTLCache___init__ : Func :=
  { name := "cachetools/func.py:<module>._UnboundTTLCache.__init__"
  , params := ["ttl", "timer"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["ttl", "timer"], isMethod := some true }
  , body := (.seq
            (.expr
              (.mcall
                (.field (.name "<module>cachetools/func.py") "TTLCache")
                "__init__"
                [ (.name "self")
                , (.field (.field (.name "<module>cachetools/func.py") "math") "inf")
                , (.name "ttl")
                , (.name "timer") ]))
            (.seq .skip .skip)) }

/-- `cachetools/func.py:<module>._UnboundTTLCache.maxsize`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module___UnboundTTLCache_maxsize : Func :=
  { name := "cachetools/func.py:<module>._UnboundTTLCache.maxsize"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.ret (.lit .unit)) }

/-- `cachetools/func.py:<module>._cache`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module___cache : Func :=
  { name := "cachetools/func.py:<module>._cache"
  , params := ["cache", "maxsize", "typed"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["cache", "maxsize", "typed"], isMethod := some false }
  , body := (.seq
            (.assign "decorator" (.closure "cachetools/func.py:<module>._cache.decorator"))
            (.seq (.ret (.name "decorator")) (.seq .skip (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/func.py:<module>._cache.decorator`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module___cache_decorator : Func :=
  { name := "cachetools/func.py:<module>._cache.decorator"
  , params := ["func"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["func"], isMethod := some false }
  , body := (.seq
            (.assign
              "key"
              (.cond
                (.name "typed")
                (.field (.field (.name "<module>cachetools/func.py") "keys") "typedkey")
                (.field (.field (.name "<module>cachetools/func.py") "keys") "hashkey")))
            (.seq
              (.assign
                "wrapper"
                (.callValue
                  (.callValue
                    (.field (.name "<module>cachetools/func.py") "cached")
                    [ (.kwargE "cache" (.name "cache"))
                    , (.kwargE "key" (.name "key"))
                    , (.kwargE
                        "condition"
                        (.callValue (.field (.name "<module>cachetools/func.py") "Condition") []))
                    , (.kwargE "info" (.lit (.bool true))) ])
                  [(.name "func")]))
              (.seq
                (.setField
                  (.name "wrapper")
                  "cache_parameters"
                  (.closure "cachetools/func.py:<module>._cache.decorator.<lambda>0"))
                (.seq
                  .skip
                  (.seq
                    (.ret (.name "wrapper"))
                    (.seq
                      .skip
                      (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))) }

/-- `cachetools/func.py:<module>._cache.decorator.<lambda>0`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module___cache_decorator__lambda_0 : Func :=
  { name := "cachetools/func.py:<module>._cache.decorator.<lambda>0"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            (.seq
              (.assign "tmp0" (.dictE []))
              (.seq
                (.setIndex (.name "tmp0") (.lit (.str "maxsize")) (.name "maxsize"))
                (.seq
                  (.setIndex (.name "tmp0") (.lit (.str "typed")) (.name "typed"))
                  (.ret (.name "tmp0")))))
            (.seq .skip (.seq .skip .skip))) }

/-- `cachetools/func.py:<module>.fifo_cache`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module__fifo_cache : Func :=
  { name := "cachetools/func.py:<module>.fifo_cache"
  , params := ["maxsize", "typed"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false, defaults := [("maxsize", (.lit (.int 128))), ("typed", (.lit (.bool false)))] }
  , body := (.seq
            (.expr
              (.lit
                (.str "Decorator to wrap a function with a memoizing callable that saves\n    up to `maxsize` results based on a First In First Out (FIFO)\n    algorithm.\n\n    ")))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.isOp false (.name "maxsize") (.lit .unit))
                  (.seq
                    (.assign "$exprV$244" (.field (.name "<module>cachetools/func.py") "_cache"))
                    (.seq
                      (.assign "tmp0" (.dictE []))
                      (.ret
                        (.callValue
                          (.name "$exprV$244")
                          [(.name "tmp0"), (.lit .unit), (.name "typed")]))))
                  (.ifte
                    (.call "callable" [(.name "maxsize")])
                    (.ret
                      (.callValue
                        (.callValue
                          (.field (.name "<module>cachetools/func.py") "_cache")
                          [ (.callValue
                              (.field (.name "<module>cachetools/func.py") "FIFOCache")
                              [(.lit (.int 128))])
                          , (.lit (.int 128))
                          , (.name "typed") ])
                        [(.name "maxsize")]))
                    (.ret
                      (.callValue
                        (.field (.name "<module>cachetools/func.py") "_cache")
                        [ (.callValue
                            (.field (.name "<module>cachetools/func.py") "FIFOCache")
                            [(.name "maxsize")])
                        , (.name "maxsize")
                        , (.name "typed") ]))))
                (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/func.py:<module>.lfu_cache`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module__lfu_cache : Func :=
  { name := "cachetools/func.py:<module>.lfu_cache"
  , params := ["maxsize", "typed"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false, defaults := [("maxsize", (.lit (.int 128))), ("typed", (.lit (.bool false)))] }
  , body := (.seq
            (.expr
              (.lit
                (.str "Decorator to wrap a function with a memoizing callable that saves\n    up to `maxsize` results based on a Least Frequently Used (LFU)\n    algorithm.\n\n    ")))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.isOp false (.name "maxsize") (.lit .unit))
                  (.seq
                    (.assign "$exprV$245" (.field (.name "<module>cachetools/func.py") "_cache"))
                    (.seq
                      (.assign "tmp0" (.dictE []))
                      (.ret
                        (.callValue
                          (.name "$exprV$245")
                          [(.name "tmp0"), (.lit .unit), (.name "typed")]))))
                  (.ifte
                    (.call "callable" [(.name "maxsize")])
                    (.ret
                      (.callValue
                        (.callValue
                          (.field (.name "<module>cachetools/func.py") "_cache")
                          [ (.callValue
                              (.field (.name "<module>cachetools/func.py") "LFUCache")
                              [(.lit (.int 128))])
                          , (.lit (.int 128))
                          , (.name "typed") ])
                        [(.name "maxsize")]))
                    (.ret
                      (.callValue
                        (.field (.name "<module>cachetools/func.py") "_cache")
                        [ (.callValue
                            (.field (.name "<module>cachetools/func.py") "LFUCache")
                            [(.name "maxsize")])
                        , (.name "maxsize")
                        , (.name "typed") ]))))
                (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/func.py:<module>.lru_cache`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module__lru_cache : Func :=
  { name := "cachetools/func.py:<module>.lru_cache"
  , params := ["maxsize", "typed"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false, defaults := [("maxsize", (.lit (.int 128))), ("typed", (.lit (.bool false)))] }
  , body := (.seq
            (.expr
              (.lit
                (.str "Decorator to wrap a function with a memoizing callable that saves\n    up to `maxsize` results based on a Least Recently Used (LRU)\n    algorithm.\n\n    ")))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.isOp false (.name "maxsize") (.lit .unit))
                  (.seq
                    (.assign "$exprV$246" (.field (.name "<module>cachetools/func.py") "_cache"))
                    (.seq
                      (.assign "tmp0" (.dictE []))
                      (.ret
                        (.callValue
                          (.name "$exprV$246")
                          [(.name "tmp0"), (.lit .unit), (.name "typed")]))))
                  (.ifte
                    (.call "callable" [(.name "maxsize")])
                    (.ret
                      (.callValue
                        (.callValue
                          (.field (.name "<module>cachetools/func.py") "_cache")
                          [ (.callValue
                              (.field (.name "<module>cachetools/func.py") "LRUCache")
                              [(.lit (.int 128))])
                          , (.lit (.int 128))
                          , (.name "typed") ])
                        [(.name "maxsize")]))
                    (.ret
                      (.callValue
                        (.field (.name "<module>cachetools/func.py") "_cache")
                        [ (.callValue
                            (.field (.name "<module>cachetools/func.py") "LRUCache")
                            [(.name "maxsize")])
                        , (.name "maxsize")
                        , (.name "typed") ]))))
                (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/func.py:<module>.rr_cache`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module__rr_cache : Func :=
  { name := "cachetools/func.py:<module>.rr_cache"
  , params := ["maxsize", "choice", "typed"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false, defaults := [("maxsize", (.lit (.int 128))), ("choice", (.fnref "cachetools/__init__.py:<module>.RRCache.choice")), ("typed", (.lit (.bool false)))] }
  , body := (.seq
            (.expr
              (.lit
                (.str "Decorator to wrap a function with a memoizing callable that saves\n    up to `maxsize` results based on a Random Replacement (RR)\n    algorithm.\n\n    ")))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.isOp false (.name "maxsize") (.lit .unit))
                  (.seq
                    (.assign "$exprV$247" (.field (.name "<module>cachetools/func.py") "_cache"))
                    (.seq
                      (.assign "tmp0" (.dictE []))
                      (.ret
                        (.callValue
                          (.name "$exprV$247")
                          [(.name "tmp0"), (.lit .unit), (.name "typed")]))))
                  (.ifte
                    (.call "callable" [(.name "maxsize")])
                    (.ret
                      (.callValue
                        (.callValue
                          (.field (.name "<module>cachetools/func.py") "_cache")
                          [ (.callValue
                              (.field (.name "<module>cachetools/func.py") "RRCache")
                              [(.lit (.int 128)), (.name "choice")])
                          , (.lit (.int 128))
                          , (.name "typed") ])
                        [(.name "maxsize")]))
                    (.ret
                      (.callValue
                        (.field (.name "<module>cachetools/func.py") "_cache")
                        [ (.callValue
                            (.field (.name "<module>cachetools/func.py") "RRCache")
                            [(.name "maxsize"), (.name "choice")])
                        , (.name "maxsize")
                        , (.name "typed") ]))))
                (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/func.py:<module>.ttl_cache`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module__ttl_cache : Func :=
  { name := "cachetools/func.py:<module>.ttl_cache"
  , params := ["maxsize", "ttl", "timer", "typed"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false, defaults := [("maxsize", (.lit (.int 128))), ("ttl", (.lit (.int 600))), ("timer", (.fnref "<absent:external>time.monotonic")), ("typed", (.lit (.bool false)))] }
  , body := (.seq
            (.expr
              (.lit
                (.str "Decorator to wrap a function with a memoizing callable that saves\n    up to `maxsize` results based on a Least Recently Used (LRU)\n    algorithm with a per-item time-to-live (TTL) value.\n\n    ")))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.isOp false (.name "maxsize") (.lit .unit))
                  (.ret
                    (.callValue
                      (.field (.name "<module>cachetools/func.py") "_cache")
                      [ (.alloc
                          "cachetools/func.py:<module>._UnboundTTLCache"
                          [(.name "ttl"), (.name "timer")])
                      , (.lit .unit)
                      , (.name "typed") ]))
                  (.ifte
                    (.call "callable" [(.name "maxsize")])
                    (.ret
                      (.callValue
                        (.callValue
                          (.field (.name "<module>cachetools/func.py") "_cache")
                          [ (.callValue
                              (.field (.name "<module>cachetools/func.py") "TTLCache")
                              [(.lit (.int 128)), (.name "ttl"), (.name "timer")])
                          , (.lit (.int 128))
                          , (.name "typed") ])
                        [(.name "maxsize")]))
                    (.ret
                      (.callValue
                        (.field (.name "<module>cachetools/func.py") "_cache")
                        [ (.callValue
                            (.field (.name "<module>cachetools/func.py") "TTLCache")
                            [(.name "maxsize"), (.name "ttl"), (.name "timer")])
                        , (.name "maxsize")
                        , (.name "typed") ]))))
                (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/keys.py:<module>._HashedTuple.__hash__`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module___HashedTuple___hash__ : Func :=
  { name := "cachetools/keys.py:<module>._HashedTuple.__hash__"
  , params := ["hash"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true, defaults := [("hash", (.fnref "cachetools/keys.py:<module>._HashedTuple.__hash__"))] }
  , body := (.seq
            (.assign "hashvalue" (.field (.name "self") "_HashedTuple__hashvalue"))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.isOp false (.name "hashvalue") (.lit .unit))
                  (.seq
                    (.assign "tmp0" (.callValue (.name "hash") [(.name "self")]))
                    (.seq
                      (.setField (.name "self") "_HashedTuple__hashvalue" (.name "tmp0"))
                      (.assign "hashvalue" (.name "tmp0"))))
                  .skip)
                (.seq .skip (.ret (.name "hashvalue")))))) }

/-- `cachetools/keys.py:<module>._HashedTuple.__add__`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module___HashedTuple___add__ : Func :=
  { name := "cachetools/keys.py:<module>._HashedTuple.__add__"
  , params := ["other", "add"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["other"], isMethod := some true, defaults := [("add", (.fnref "cachetools/keys.py:<module>._HashedTuple.__add__"))] }
  , body := (.seq
            (.ret
              (.alloc
                "cachetools/keys.py:<module>._HashedTuple"
                [(.callValue (.name "add") [(.name "self"), (.name "other")])]))
            .skip) }

/-- `cachetools/keys.py:<module>._HashedTuple.__radd__`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module___HashedTuple___radd__ : Func :=
  { name := "cachetools/keys.py:<module>._HashedTuple.__radd__"
  , params := ["other", "add"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["other"], isMethod := some true, defaults := [("add", (.fnref "cachetools/keys.py:<module>._HashedTuple.__add__"))] }
  , body := (.seq
            (.ret
              (.alloc
                "cachetools/keys.py:<module>._HashedTuple"
                [(.callValue (.name "add") [(.name "other"), (.name "self")])]))
            .skip) }

/-- `cachetools/keys.py:<module>._HashedTuple.__getstate__`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module___HashedTuple___getstate__ : Func :=
  { name := "cachetools/keys.py:<module>._HashedTuple.__getstate__"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.seq (.seq (.assign "tmp0" (.dictE [])) (.ret (.name "tmp0"))) .skip) }

/-- `cachetools/keys.py:<module>.hashkey`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module__hashkey : Func :=
  { name := "cachetools/keys.py:<module>.hashkey"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            (.expr (.lit (.str "Return a cache key for the specified hashable arguments.")))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.name "kwargs")
                  (.ret
                    (.alloc
                      "cachetools/keys.py:<module>._HashedTuple"
                      [ (.binop
                          "+"
                          (.binop
                            "+"
                            (.name "args")
                            (.field (.name "<module>cachetools/keys.py") "_kwmark"))
                          (.call "tuple" [(.call "sorted" [(.mcall (.name "kwargs") "items" [])])])) ]))
                  (.ret (.alloc "cachetools/keys.py:<module>._HashedTuple" [(.name "args")])))
                (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/keys.py:<module>.methodkey`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module__methodkey : Func :=
  { name := "cachetools/keys.py:<module>.methodkey"
  , params := ["self", "args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["self"], isMethod := some false }
  , body := (.seq
            (.expr (.lit (.str "Return a cache key for use with cached methods.")))
            (.seq
              .skip
              (.ret
                (.callValue
                  (.field (.name "<module>cachetools/keys.py") "hashkey")
                  [(.starred (.name "args")), (.dstarred (.name "kwargs"))])))) }

/-- `cachetools/keys.py:<module>.typedkey`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module__typedkey : Func :=
  { name := "cachetools/keys.py:<module>.typedkey"
  , params := ["args", "kwargs"]
  , analysisBody := some (.seq
            (.seq
              (.expr (.lit (.str "Return a typed cache key for the specified hashable arguments.")))
              (.seq
                .skip
                (.seq
                  (.ifte
                    (.name "kwargs")
                    (.seq
                      (.assign
                        "sorted_kwargs"
                        (.call "tuple" [(.call "sorted" [(.mcall (.name "kwargs") "items" [])])]))
                      (.seq
                        (.assign
                          "key"
                          (.alloc
                            "cachetools/keys.py:<module>._HashedTuple"
                            [ (.binop
                                "+"
                                (.binop
                                  "+"
                                  (.name "args")
                                  (.field (.name "<module>cachetools/keys.py") "_kwmark"))
                                (.name "sorted_kwargs")) ]))
                        (.seq
                          (.assign "$exprV$249" (.name "key"))
                          (.seq
                            (.assign
                              "$exprV$248"
                              (.call
                                "cachetools/keys.py:<module>.typedkey.<genexpr>0"
                                [(.call "<python-iter>" [(.name "sorted_kwargs")])]))
                            (.assign
                              "key"
                              (.binop
                                "+"
                                (.name "$exprV$249")
                                (.call "tuple" [(.name "$exprV$248")])))))))
                    (.assign
                      "key"
                      (.alloc "cachetools/keys.py:<module>._HashedTuple" [(.name "args")])))
                  (.seq
                    .skip
                    (.seq
                      (.seq
                        (.assign "$exprV$251" (.name "key"))
                        (.seq
                          (.assign
                            "$exprV$250"
                            (.call
                              "cachetools/keys.py:<module>.typedkey.<genexpr>9"
                              [(.call "<python-iter>" [(.name "args")])]))
                          (.assign
                            "key"
                            (.binop "+" (.name "$exprV$251") (.call "tuple" [(.name "$exprV$250")])))))
                      (.seq
                        .skip
                        (.seq
                          (.ret (.name "key"))
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))
            (.seq
              (.forIn
                "$comp$tmp2"
                (.name "<genexpr-iterator>")
                (.seq
                  (.assign "$comp$_" (.index (.name "$comp$tmp2") (.lit (.int 0))))
                  (.seq
                    (.assign "$comp$v" (.index (.name "$comp$tmp2") (.lit (.int 1))))
                    (.expr (.call "type" [(.name "$comp$v")])))))
              (.seq
                (.forIn
                  "$comp$v"
                  (.name "<genexpr-iterator>")
                  (.expr (.call "type" [(.name "$comp$v")])))
                .skip)))
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some false }
  , body := (.seq
            (.expr (.lit (.str "Return a typed cache key for the specified hashable arguments.")))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.name "kwargs")
                  (.seq
                    (.assign
                      "sorted_kwargs"
                      (.call "tuple" [(.call "sorted" [(.mcall (.name "kwargs") "items" [])])]))
                    (.seq
                      (.assign
                        "key"
                        (.alloc
                          "cachetools/keys.py:<module>._HashedTuple"
                          [ (.binop
                              "+"
                              (.binop
                                "+"
                                (.name "args")
                                (.field (.name "<module>cachetools/keys.py") "_kwmark"))
                              (.name "sorted_kwargs")) ]))
                      (.seq
                        (.assign "$exprV$249" (.name "key"))
                        (.seq
                          (.assign
                            "$exprV$248"
                            (.call
                              "cachetools/keys.py:<module>.typedkey.<genexpr>0"
                              [(.call "<python-iter>" [(.name "sorted_kwargs")])]))
                          (.assign
                            "key"
                            (.binop "+" (.name "$exprV$249") (.call "tuple" [(.name "$exprV$248")])))))))
                  (.assign
                    "key"
                    (.alloc "cachetools/keys.py:<module>._HashedTuple" [(.name "args")])))
                (.seq
                  .skip
                  (.seq
                    (.seq
                      (.assign "$exprV$251" (.name "key"))
                      (.seq
                        (.assign
                          "$exprV$250"
                          (.call
                            "cachetools/keys.py:<module>.typedkey.<genexpr>9"
                            [(.call "<python-iter>" [(.name "args")])]))
                        (.assign
                          "key"
                          (.binop "+" (.name "$exprV$251") (.call "tuple" [(.name "$exprV$250")])))))
                    (.seq
                      .skip
                      (.seq
                        (.ret (.name "key"))
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))) }

/-- `cachetools/keys.py:<module>.typedmethodkey`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module__typedmethodkey : Func :=
  { name := "cachetools/keys.py:<module>.typedmethodkey"
  , params := ["self", "args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["self"], isMethod := some false }
  , body := (.seq
            (.expr (.lit (.str "Return a typed cache key for use with cached methods.")))
            (.seq
              .skip
              (.ret
                (.callValue
                  (.field (.name "<module>cachetools/keys.py") "typedkey")
                  [(.starred (.name "args")), (.dstarred (.name "kwargs"))])))) }

/-- `<module-objects>:<module>`  (from ``) -/
def f__module_objects___module_ : Func :=
  { name := "<module-objects>:<module>"
  , params := []
  , body := (.seq
            (.setGlobal
              "<module>cachetools/__init__.py"
              (.alloc "<module>cachetools/__init__.py" []))
            (.seq
              (.setGlobal
                "<module>cachetools/_cached.py"
                (.alloc "<module>cachetools/_cached.py" []))
              (.seq
                (.setGlobal
                  "<module>cachetools/_cachedmethod.py"
                  (.alloc "<module>cachetools/_cachedmethod.py" []))
                (.seq
                  (.setGlobal "<module>cachetools/func.py" (.alloc "<module>cachetools/func.py" []))
                  (.seq
                    (.setGlobal
                      "<module>cachetools/keys.py"
                      (.alloc "<module>cachetools/keys.py" []))
                    (.seq
                      (.setField
                        (.name "<module>cachetools/__init__.py")
                        "cached"
                        (.fnref "cachetools/__init__.py:<module>.cached"))
                      (.seq
                        (.setField
                          (.name "<module>cachetools/__init__.py")
                          "cachedmethod"
                          (.fnref "cachetools/__init__.py:<module>.cachedmethod"))
                        (.seq
                          (.setField
                            (.name "<module>cachetools/__init__.py")
                            "Cache"
                            (.fnref "cachetools/__init__.py:<module>.Cache<meta>"))
                          (.seq
                            (.setField
                              (.name "<module>cachetools/__init__.py")
                              "FIFOCache"
                              (.fnref "cachetools/__init__.py:<module>.FIFOCache<meta>"))
                            (.seq
                              (.setField
                                (.name "<module>cachetools/__init__.py")
                                "LFUCache"
                                (.fnref "cachetools/__init__.py:<module>.LFUCache<meta>"))
                              (.seq
                                (.setField
                                  (.name "<module>cachetools/__init__.py")
                                  "LRUCache"
                                  (.fnref "cachetools/__init__.py:<module>.LRUCache<meta>"))
                                (.seq
                                  (.setField
                                    (.name "<module>cachetools/__init__.py")
                                    "RRCache"
                                    (.fnref "cachetools/__init__.py:<module>.RRCache<meta>"))
                                  (.seq
                                    (.setField
                                      (.name "<module>cachetools/__init__.py")
                                      "TLRUCache"
                                      (.fnref "cachetools/__init__.py:<module>.TLRUCache<meta>"))
                                    (.seq
                                      (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "TTLCache"
                                        (.fnref "cachetools/__init__.py:<module>.TTLCache<meta>"))
                                      (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "_DefaultSize"
                                        (.fnref
                                        "cachetools/__init__.py:<module>._DefaultSize<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "_TimedCache"
                                        (.fnref "cachetools/__init__.py:<module>._TimedCache<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "_cached"
                                        (.name "<module>cachetools/_cached.py"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "_cachedmethod"
                                        (.name "<module>cachetools/_cachedmethod.py"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "func"
                                        (.name "<module>cachetools/func.py"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "keys"
                                        (.name "<module>cachetools/keys.py"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cached.py")
                                        "_condition"
                                        (.fnref "cachetools/_cached.py:<module>._condition"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cached.py")
                                        "_condition_info"
                                        (.fnref "cachetools/_cached.py:<module>._condition_info"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cached.py")
                                        "_locked"
                                        (.fnref "cachetools/_cached.py:<module>._locked"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cached.py")
                                        "_locked_info"
                                        (.fnref "cachetools/_cached.py:<module>._locked_info"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cached.py")
                                        "_uncached"
                                        (.fnref "cachetools/_cached.py:<module>._uncached"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cached.py")
                                        "_uncached_info"
                                        (.fnref "cachetools/_cached.py:<module>._uncached_info"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cached.py")
                                        "_unlocked"
                                        (.fnref "cachetools/_cached.py:<module>._unlocked"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cached.py")
                                        "_unlocked_info"
                                        (.fnref "cachetools/_cached.py:<module>._unlocked_info"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cached.py")
                                        "_wrapper"
                                        (.fnref "cachetools/_cached.py:<module>._wrapper"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_condition"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._condition"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_condition_info"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._condition_info"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_locked"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._locked"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_locked_info"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._locked_info"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_none"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._none"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_unlocked"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._unlocked"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_unlocked_info"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._unlocked_info"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_warn_classmethod"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._warn_classmethod"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_warn_instance_dict"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._warn_instance_dict"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_wrapper"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._wrapper"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_DeprecatedDescriptorBase"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_DescriptorBase"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._DescriptorBase<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_WrapperBase"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._WrapperBase<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/func.py")
                                        "_cache"
                                        (.fnref "cachetools/func.py:<module>._cache"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/func.py")
                                        "fifo_cache"
                                        (.fnref "cachetools/func.py:<module>.fifo_cache"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/func.py")
                                        "lfu_cache"
                                        (.fnref "cachetools/func.py:<module>.lfu_cache"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/func.py")
                                        "lru_cache"
                                        (.fnref "cachetools/func.py:<module>.lru_cache"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/func.py")
                                        "rr_cache"
                                        (.fnref "cachetools/func.py:<module>.rr_cache"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/func.py")
                                        "ttl_cache"
                                        (.fnref "cachetools/func.py:<module>.ttl_cache"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/func.py")
                                        "_UnboundTTLCache"
                                        (.fnref
                                        "cachetools/func.py:<module>._UnboundTTLCache<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/keys.py")
                                        "hashkey"
                                        (.fnref "cachetools/keys.py:<module>.hashkey"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/keys.py")
                                        "methodkey"
                                        (.fnref "cachetools/keys.py:<module>.methodkey"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/keys.py")
                                        "typedkey"
                                        (.fnref "cachetools/keys.py:<module>.typedkey"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/keys.py")
                                        "typedmethodkey"
                                        (.fnref "cachetools/keys.py:<module>.typedmethodkey"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/keys.py")
                                        "_HashedTuple"
                                        (.fnref "cachetools/keys.py:<module>._HashedTuple<meta>"))
                                        (.seq
                                        (.setGlobal
                                        "<classattr>cachetools/__init__.py:<module>.Cache._Cache__marker"
                                        (.boxNew (.lit .unit)))
                                        (.seq
                                        (.setGlobal
                                        "<classattr>Cache._Cache__marker"
                                        (.name
                                        "<classattr>cachetools/__init__.py:<module>.Cache._Cache__marker"))
                                        .skip)))))))))))))))))))))))))))))))))))))))))))))))))))))))) }

/-- `cachetools/_cached.py:<module>`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module_ : Func :=
  { name := "cachetools/_cached.py:<module>"
  , params := []
  , body := (.seq
            (.setField (.name "<module>cachetools/_cached.py") "set" (.fnref "__builtin.set<meta>"))
            (.seq
              (.expr (.lit (.str "Function decorator helpers.")))
              (.seq
                (.setField (.name "<module>cachetools/_cached.py") "__all__" (.tupleE []))
                (.seq
                  (.setField
                    (.name "<module>cachetools/_cached.py")
                    "functools"
                    (.fnref "<absent:external>functools"))
                  (.seq
                    (.setField
                      (.name "<module>cachetools/_cached.py")
                      "_condition_info"
                      (.fnref "cachetools/_cached.py:<module>._condition_info"))
                    (.seq
                      (.setField
                        (.name "<module>cachetools/_cached.py")
                        "_locked_info"
                        (.fnref "cachetools/_cached.py:<module>._locked_info"))
                      (.seq
                        (.setField
                          (.name "<module>cachetools/_cached.py")
                          "_unlocked_info"
                          (.fnref "cachetools/_cached.py:<module>._unlocked_info"))
                        (.seq
                          (.setField
                            (.name "<module>cachetools/_cached.py")
                            "_uncached_info"
                            (.fnref "cachetools/_cached.py:<module>._uncached_info"))
                          (.seq
                            (.setField
                              (.name "<module>cachetools/_cached.py")
                              "_condition"
                              (.fnref "cachetools/_cached.py:<module>._condition"))
                            (.seq
                              (.setField
                                (.name "<module>cachetools/_cached.py")
                                "_locked"
                                (.fnref "cachetools/_cached.py:<module>._locked"))
                              (.seq
                                (.setField
                                  (.name "<module>cachetools/_cached.py")
                                  "_unlocked"
                                  (.fnref "cachetools/_cached.py:<module>._unlocked"))
                                (.seq
                                  (.setField
                                    (.name "<module>cachetools/_cached.py")
                                    "_uncached"
                                    (.fnref "cachetools/_cached.py:<module>._uncached"))
                                  (.seq
                                    (.setField
                                      (.name "<module>cachetools/_cached.py")
                                      "_wrapper"
                                      (.fnref "cachetools/_cached.py:<module>._wrapper"))
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module_ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>"
  , params := []
  , body := (.seq
            (.setField
              (.name "<module>cachetools/_cachedmethod.py")
              "isinstance"
              (.fnref "__builtin.isinstance"))
            (.seq
              (.setField
                (.name "<module>cachetools/_cachedmethod.py")
                "super"
                (.fnref "__builtin.super"))
              (.seq
                (.setField
                  (.name "<module>cachetools/_cachedmethod.py")
                  "property"
                  (.fnref "__builtin.property<meta>"))
                (.seq
                  (.setField
                    (.name "<module>cachetools/_cachedmethod.py")
                    "set"
                    (.fnref "__builtin.set<meta>"))
                  (.seq
                    (.setField
                      (.name "<module>cachetools/_cachedmethod.py")
                      "type"
                      (.fnref "__builtin.type<meta>"))
                    (.seq
                      (.expr (.lit (.str "Method decorator helpers.")))
                      (.seq
                        (.setField
                          (.name "<module>cachetools/_cachedmethod.py")
                          "__all__"
                          (.tupleE []))
                        (.seq
                          (.setField
                            (.name "<module>cachetools/_cachedmethod.py")
                            "functools"
                            (.fnref "<absent:external>functools"))
                          (.seq
                            (.setField
                              (.name "<module>cachetools/_cachedmethod.py")
                              "warnings"
                              (.fnref "<absent:external>warnings"))
                            (.seq
                              (.setField
                                (.name "<module>cachetools/_cachedmethod.py")
                                "weakref"
                                (.fnref "<absent:external>weakref"))
                              (.seq
                                (.setField
                                  (.name "<module>cachetools/_cachedmethod.py")
                                  "_warn_classmethod"
                                  (.fnref "cachetools/_cachedmethod.py:<module>._warn_classmethod"))
                                (.seq
                                  (.setField
                                    (.name "<module>cachetools/_cachedmethod.py")
                                    "_warn_instance_dict"
                                    (.fnref
                                      "cachetools/_cachedmethod.py:<module>._warn_instance_dict"))
                                  (.seq
                                    (.setField
                                      (.name "<module>cachetools/_cachedmethod.py")
                                      "_none"
                                      (.fnref "cachetools/_cachedmethod.py:<module>._none"))
                                    (.seq
                                      (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_WrapperBase"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._WrapperBase<meta>"))
                                        (.expr
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._WrapperBase<meta>")))
                                      (.seq
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_DescriptorBase"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._DescriptorBase<meta>"))
                                        (.expr
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._DescriptorBase<meta>")))
                                        (.seq
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_DeprecatedDescriptorBase"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase<meta>"))
                                        (.expr
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase<meta>")))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_condition_info"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._condition_info"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_locked_info"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._locked_info"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_unlocked_info"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._unlocked_info"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_condition"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._condition"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_locked"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._locked"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_unlocked"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._unlocked"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_wrapper"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._wrapper"))
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))))))))))))))))))))))))))))))))))))) }

/-- `cachetools/__init__.py:<module>`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module_ : Func :=
  { name := "cachetools/__init__.py:<module>"
  , params := []
  , body := (.seq
            (.setField
              (.name "<module>cachetools/__init__.py")
              "getattr"
              (.fnref "__builtin.getattr"))
            (.seq
              (.setField
                (.name "<module>cachetools/__init__.py")
                "isinstance"
                (.fnref "__builtin.isinstance"))
              (.seq
                (.setField
                  (.name "<module>cachetools/__init__.py")
                  "iter"
                  (.fnref "__builtin.iter"))
                (.seq
                  (.setField
                    (.name "<module>cachetools/__init__.py")
                    "len"
                    (.fnref "__builtin.len"))
                  (.seq
                    (.setField
                      (.name "<module>cachetools/__init__.py")
                      "next"
                      (.fnref "__builtin.next"))
                    (.seq
                      (.setField
                        (.name "<module>cachetools/__init__.py")
                        "repr"
                        (.fnref "__builtin.repr"))
                      (.seq
                        (.setField
                          (.name "<module>cachetools/__init__.py")
                          "sorted"
                          (.fnref "__builtin.sorted"))
                        (.seq
                          (.setField
                            (.name "<module>cachetools/__init__.py")
                            "staticmethod"
                            (.fnref "__builtin.staticmethod"))
                          (.seq
                            (.setField
                              (.name "<module>cachetools/__init__.py")
                              "super"
                              (.fnref "__builtin.super"))
                            (.seq
                              (.setField
                                (.name "<module>cachetools/__init__.py")
                                "object"
                                (.fnref "__builtin.object<meta>"))
                              (.seq
                                (.setField
                                  (.name "<module>cachetools/__init__.py")
                                  "property"
                                  (.fnref "__builtin.property<meta>"))
                                (.seq
                                  (.setField
                                    (.name "<module>cachetools/__init__.py")
                                    "set"
                                    (.fnref "__builtin.set<meta>"))
                                  (.seq
                                    (.setField
                                      (.name "<module>cachetools/__init__.py")
                                      "type"
                                      (.fnref "__builtin.type<meta>"))
                                    (.seq
                                      (.expr
                                        (.lit
                                        (.str "Extensible memoizing collections and decorators.")))
                                      (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "__all__"
                                        (.tupleE
                                        [ (.lit (.str "Cache"))
                                        , (.lit (.str "FIFOCache"))
                                        , (.lit (.str "LFUCache"))
                                        , (.lit (.str "LRUCache"))
                                        , (.lit (.str "RRCache"))
                                        , (.lit (.str "TLRUCache"))
                                        , (.lit (.str "TTLCache"))
                                        , (.lit (.str "cached"))
                                        , (.lit (.str "cachedmethod")) ]))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "__version__"
                                        (.lit (.str "7.1.7")))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "collections"
                                        (.fnref "<absent:external>collections"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "collections"
                                        (.fnref "<absent:external>collections"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "functools"
                                        (.fnref "<absent:external>functools"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "heapq"
                                        (.fnref "<absent:external>heapq"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "random"
                                        (.fnref "<absent:external>random"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "time"
                                        (.fnref "<absent:external>time"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "keys"
                                        (.name "<module>cachetools/keys.py"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "_DefaultSize"
                                        (.fnref
                                        "cachetools/__init__.py:<module>._DefaultSize<meta>"))
                                        (.expr
                                        (.fnref
                                        "cachetools/__init__.py:<module>._DefaultSize<meta>")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "Cache"
                                        (.fnref "cachetools/__init__.py:<module>.Cache<meta>"))
                                        (.expr
                                        (.fnref "cachetools/__init__.py:<module>.Cache<meta>")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "FIFOCache"
                                        (.fnref "cachetools/__init__.py:<module>.FIFOCache<meta>"))
                                        (.expr
                                        (.fnref "cachetools/__init__.py:<module>.FIFOCache<meta>")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "LFUCache"
                                        (.fnref "cachetools/__init__.py:<module>.LFUCache<meta>"))
                                        (.expr
                                        (.fnref "cachetools/__init__.py:<module>.LFUCache<meta>")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "LRUCache"
                                        (.fnref "cachetools/__init__.py:<module>.LRUCache<meta>"))
                                        (.expr
                                        (.fnref "cachetools/__init__.py:<module>.LRUCache<meta>")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "RRCache"
                                        (.fnref "cachetools/__init__.py:<module>.RRCache<meta>"))
                                        (.expr
                                        (.fnref "cachetools/__init__.py:<module>.RRCache<meta>")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "_TimedCache"
                                        (.fnref "cachetools/__init__.py:<module>._TimedCache<meta>"))
                                        (.expr
                                        (.fnref "cachetools/__init__.py:<module>._TimedCache<meta>")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "TTLCache"
                                        (.fnref "cachetools/__init__.py:<module>.TTLCache<meta>"))
                                        (.expr
                                        (.fnref "cachetools/__init__.py:<module>.TTLCache<meta>")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "TLRUCache"
                                        (.fnref "cachetools/__init__.py:<module>.TLRUCache<meta>"))
                                        (.expr
                                        (.fnref "cachetools/__init__.py:<module>.TLRUCache<meta>")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "_CacheInfo"
                                        (.mcall
                                        (.field
                                        (.name "<module>cachetools/__init__.py")
                                        "collections")
                                        "namedtuple"
                                        [ (.lit (.str "CacheInfo"))
                                        , (.listE
                                        [ (.lit (.str "hits"))
                                        , (.lit (.str "misses"))
                                        , (.lit (.str "maxsize"))
                                        , (.lit (.str "currsize")) ]) ]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "cached"
                                        (.fnref "cachetools/__init__.py:<module>.cached"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "cachedmethod"
                                        (.fnref "cachetools/__init__.py:<module>.cachedmethod"))
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) }

/-- `cachetools/func.py:<module>`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module_ : Func :=
  { name := "cachetools/func.py:<module>"
  , params := []
  , body := (.seq
            (.setField
              (.name "<module>cachetools/func.py")
              "callable"
              (.fnref "__builtin.callable"))
            (.seq
              (.setField
                (.name "<module>cachetools/func.py")
                "property"
                (.fnref "__builtin.property<meta>"))
              (.seq
                (.expr
                  (.lit (.str "`functools.lru_cache` compatible memoizing function decorators.")))
                (.seq
                  (.setField
                    (.name "<module>cachetools/func.py")
                    "__all__"
                    (.tupleE
                      [ (.lit (.str "fifo_cache"))
                      , (.lit (.str "lfu_cache"))
                      , (.lit (.str "lru_cache"))
                      , (.lit (.str "rr_cache"))
                      , (.lit (.str "ttl_cache")) ]))
                  (.seq
                    (.setField
                      (.name "<module>cachetools/func.py")
                      "math"
                      (.fnref "<absent:external>math"))
                    (.seq
                      (.setField
                        (.name "<module>cachetools/func.py")
                        "random"
                        (.fnref "<absent:external>random"))
                      (.seq
                        (.setField
                          (.name "<module>cachetools/func.py")
                          "time"
                          (.fnref "<absent:external>time"))
                        (.seq
                          (.setField
                            (.name "<module>cachetools/func.py")
                            "Condition"
                            (.fnref "<absent:external>threading"))
                          (.seq
                            (.seq
                              (.setField
                                (.name "<module>cachetools/func.py")
                                "FIFOCache"
                                (.field (.name "<module>cachetools/__init__.py") "FIFOCache"))
                              (.seq
                                (.setField
                                  (.name "<module>cachetools/func.py")
                                  "LFUCache"
                                  (.field (.name "<module>cachetools/__init__.py") "LFUCache"))
                                (.seq
                                  (.setField
                                    (.name "<module>cachetools/func.py")
                                    "LRUCache"
                                    (.field (.name "<module>cachetools/__init__.py") "LRUCache"))
                                  (.seq
                                    (.setField
                                      (.name "<module>cachetools/func.py")
                                      "RRCache"
                                      (.field (.name "<module>cachetools/__init__.py") "RRCache"))
                                    (.seq
                                      (.setField
                                        (.name "<module>cachetools/func.py")
                                        "TTLCache"
                                        (.field (.name "<module>cachetools/__init__.py") "TTLCache"))
                                      (.seq
                                        (.setField
                                        (.name "<module>cachetools/func.py")
                                        "cached"
                                        (.field (.name "<module>cachetools/__init__.py") "cached"))
                                        (.setField
                                        (.name "<module>cachetools/func.py")
                                        "keys"
                                        (.name "<module>cachetools/keys.py"))))))))
                            (.seq
                              (.seq
                                (.setField
                                  (.name "<module>cachetools/func.py")
                                  "_UnboundTTLCache"
                                  (.fnref "cachetools/func.py:<module>._UnboundTTLCache<meta>"))
                                (.expr
                                  (.fnref "cachetools/func.py:<module>._UnboundTTLCache<meta>")))
                              (.seq
                                (.setField
                                  (.name "<module>cachetools/func.py")
                                  "_cache"
                                  (.fnref "cachetools/func.py:<module>._cache"))
                                (.seq
                                  (.setField
                                    (.name "<module>cachetools/func.py")
                                    "fifo_cache"
                                    (.fnref "cachetools/func.py:<module>.fifo_cache"))
                                  (.seq
                                    (.setField
                                      (.name "<module>cachetools/func.py")
                                      "lfu_cache"
                                      (.fnref "cachetools/func.py:<module>.lfu_cache"))
                                    (.seq
                                      (.setField
                                        (.name "<module>cachetools/func.py")
                                        "lru_cache"
                                        (.fnref "cachetools/func.py:<module>.lru_cache"))
                                      (.seq
                                        (.setField
                                        (.name "<module>cachetools/func.py")
                                        "rr_cache"
                                        (.fnref "cachetools/func.py:<module>.rr_cache"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/func.py")
                                        "ttl_cache"
                                        (.fnref "cachetools/func.py:<module>.ttl_cache"))
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))))))))))))))))))))))))) }

/-- `cachetools/keys.py:<module>`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module_ : Func :=
  { name := "cachetools/keys.py:<module>"
  , params := []
  , body := (.seq
            (.setField (.name "<module>cachetools/keys.py") "hash" (.fnref "__builtin.hash"))
            (.seq
              (.setField (.name "<module>cachetools/keys.py") "sorted" (.fnref "__builtin.sorted"))
              (.seq
                (.setField
                  (.name "<module>cachetools/keys.py")
                  "tuple"
                  (.fnref "__builtin.tuple<meta>"))
                (.seq
                  (.setField
                    (.name "<module>cachetools/keys.py")
                    "type"
                    (.fnref "__builtin.type<meta>"))
                  (.seq
                    (.expr (.lit (.str "Key functions for memoizing decorators.")))
                    (.seq
                      (.setField
                        (.name "<module>cachetools/keys.py")
                        "__all__"
                        (.tupleE
                          [ (.lit (.str "hashkey"))
                          , (.lit (.str "methodkey"))
                          , (.lit (.str "typedkey"))
                          , (.lit (.str "typedmethodkey")) ]))
                      (.seq
                        (.seq
                          (.setField
                            (.name "<module>cachetools/keys.py")
                            "_HashedTuple"
                            (.fnref "cachetools/keys.py:<module>._HashedTuple<meta>"))
                          (.expr (.fnref "cachetools/keys.py:<module>._HashedTuple<meta>")))
                        (.seq
                          (.setField
                            (.name "<module>cachetools/keys.py")
                            "_kwmark"
                            (.tupleE [(.field (.name "<module>cachetools/keys.py") "_HashedTuple")]))
                          (.seq
                            (.setField
                              (.name "<module>cachetools/keys.py")
                              "hashkey"
                              (.fnref "cachetools/keys.py:<module>.hashkey"))
                            (.seq
                              (.setField
                                (.name "<module>cachetools/keys.py")
                                "methodkey"
                                (.fnref "cachetools/keys.py:<module>.methodkey"))
                              (.seq
                                (.setField
                                  (.name "<module>cachetools/keys.py")
                                  "typedkey"
                                  (.fnref "cachetools/keys.py:<module>.typedkey"))
                                (.seq
                                  .skip
                                  (.seq
                                    (.setField
                                      (.name "<module>cachetools/keys.py")
                                      "typedmethodkey"
                                      (.fnref "cachetools/keys.py:<module>.typedmethodkey"))
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))))))) }

/-- `<autoform>.<generator>.__init__`  (from ``) -/
def f__autoform___generator____init__ : Func :=
  { name := "<autoform>.<generator>.__init__"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := .skip }

/-- `<autoform>.<generator>.__iter__`  (from ``) -/
def f__autoform___generator____iter__ : Func :=
  { name := "<autoform>.<generator>.__iter__"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.ret (.name "self")) }

/-- `<autoform>.<generator>.__read_local__`  (from ``) -/
def f__autoform___generator____read_local__ : Func :=
  { name := "<autoform>.<generator>.__read_local__"
  , params := ["key"]
  , pythonSignature := some { positionalOnly := ["key"], keywordOnly := [], required := ["key"], isMethod := some true }
  , body := (.tryCatch
            (.ret (.index (.field (.name "self") "<locals>") (.name "key")))
            "<lookup-error>"
            (.ifte
              (.binop "==" (.name "<lookup-error>") (.lit (.str "KeyError")))
              (.raise (.unop "py:exception:UnboundLocalError" (.tupleE [])))
              (.raise (.name "<lookup-error>")))) }

/-- `<autoform>.<generator>.__next__`  (from ``) -/
def f__autoform___generator____next__ : Func :=
  { name := "<autoform>.<generator>.__next__"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.ret (.callValue (.field (.name "self") "<resume>") [(.name "self"), (.lit .unit)])) }

/-- `<autoform>.<generator>.send`  (from ``) -/
def f__autoform___generator__send : Func :=
  { name := "<autoform>.<generator>.send"
  , params := ["value"]
  , pythonSignature := some { positionalOnly := ["value"], keywordOnly := [], required := ["value"], isMethod := some true }
  , body := (.ret (.callValue (.field (.name "self") "<resume>") [(.name "self"), (.name "value")])) }

/-- `<autoform>.<generator>.close`  (from ``) -/
def f__autoform___generator__close : Func :=
  { name := "<autoform>.<generator>.close"
  , params := []
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.hole "generator:close") }

/-- `<autoform>.<generator>.throw`  (from ``) -/
def f__autoform___generator__throw : Func :=
  { name := "<autoform>.<generator>.throw"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := [], isMethod := some true }
  , body := (.hole "generator:throw") }

/-- `<generator>.cachetools/__init__.py:<module>.TTLCache.__iter__.<resume>`  (from ``) -/
def f__generator__cachetools___init___py__module__TTLCache___iter____resume_ : Func :=
  { name := "<generator>.cachetools/__init__.py:<module>.TTLCache.__iter__.<resume>"
  , params := ["self", "value"]
  , pythonSignature := some { positionalOnly := ["self", "value"], keywordOnly := [], required := ["self", "value"], isMethod := some false }
  , body := (.ifte
            (.binop "==" (.field (.name "self") "<state>") (.lit (.int 3)))
            (.raise (.unop "py:exception:StopIteration" (.tupleE [])))
            (.ifte
              (.binop "==" (.field (.name "self") "<state>") (.lit (.int 2)))
              (.raise (.unop "py:exception:ValueError" (.tupleE [])))
              (.ifte
                (.cond
                  (.binop "==" (.field (.name "self") "<state>") (.lit (.int 0)))
                  (.cond
                    (.binop "!=" (.name "value") (.lit .unit))
                    (.lit (.bool true))
                    (.lit (.bool false)))
                  (.lit (.bool false)))
                (.raise (.unop "py:exception:TypeError" (.tupleE [])))
                (.seq
                  (.setField (.name "self") "<sent>" (.name "value"))
                  (.seq
                    (.setField (.name "self") "<state>" (.lit (.int 2)))
                    (.seq
                      (.loop
                        (.lit (.bool true))
                        (.ifte
                          (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 1)))
                          (.tryCatch
                            (.ifte
                              (.isOp
                                true
                                (.mcall (.name "self") "__read_local__" [(.lit (.str "curr"))])
                                (.mcall (.name "self") "__read_local__" [(.lit (.str "root"))]))
                              (.setField (.name "self") "<pc>" (.lit (.int 17)))
                              (.setField (.name "self") "<pc>" (.lit (.int (-1)))))
                            "<caught>"
                            (.seq
                              (.setField (.name "self") "<exception>" (.name "<caught>"))
                              (.seq (.setField (.name "self") "<pc>" (.lit (.int (-2)))) .skip)))
                          (.ifte
                            (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 2)))
                            (.tryCatch
                              (.seq
                                (.setIndex
                                  (.field (.name "self") "<locals>")
                                  (.lit (.str "curr"))
                                  (.field
                                    (.mcall (.name "self") "__read_local__" [(.lit (.str "curr"))])
                                    "next"))
                                (.seq (.setField (.name "self") "<pc>" (.lit (.int 1))) .skip))
                              "<caught>"
                              (.seq
                                (.setField (.name "self") "<exception>" (.name "<caught>"))
                                (.seq (.setField (.name "self") "<pc>" (.lit (.int (-2)))) .skip)))
                            (.ifte
                              (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 3)))
                              (.tryCatch
                                (.seq
                                  (.setField
                                    (.name "self")
                                    "<exception>"
                                    (.mcall
                                      (.name "self")
                                      "__read_local__"
                                      [(.lit (.str "<generator-temp>9"))]))
                                  (.seq (.setField (.name "self") "<pc>" (.lit (.int (-2)))) .skip))
                                "<caught>"
                                (.seq
                                  (.setField (.name "self") "<exception>" (.name "<caught>"))
                                  (.seq (.setField (.name "self") "<pc>" (.lit (.int (-2)))) .skip)))
                              (.ifte
                                (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 4)))
                                (.tryCatch
                                  (.seq
                                    (.expr
                                      (.mcall
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "manager_tmp0"))])
                                        "__exit__"
                                        []))
                                    (.seq (.setField (.name "self") "<pc>" (.lit (.int 3))) .skip))
                                  "<caught>"
                                  (.seq
                                    (.setField (.name "self") "<exception>" (.name "<caught>"))
                                    (.seq
                                      (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                      .skip)))
                                (.ifte
                                  (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 5)))
                                  (.tryCatch
                                    (.seq
                                      (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "<generator-temp>9"))
                                        (.field (.name "self") "<exception>"))
                                      (.seq (.setField (.name "self") "<pc>" (.lit (.int 4))) .skip))
                                    "<caught>"
                                    (.seq
                                      (.setField (.name "self") "<exception>" (.name "<caught>"))
                                      (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                  (.ifte
                                    (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 6)))
                                    (.tryCatch
                                      (.seq
                                        (.expr
                                        (.mcall
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "manager_tmp0"))])
                                        "__exit__"
                                        []))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 2)))
                                        .skip))
                                      "<caught>"
                                      (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                    (.ifte
                                      (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 7)))
                                      (.tryCatch
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "manager_tmp0"))])
                                        "__exit__"
                                        []))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-1))))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                      (.ifte
                                        (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 8)))
                                        (.tryCatch
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "manager_tmp0"))])
                                        "__exit__"
                                        []))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 1)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                        (.ifte
                                        (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 9)))
                                        (.tryCatch
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "manager_tmp0"))])
                                        "__exit__"
                                        []))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-1))))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 10)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "$exprV$182"))
                                        (.field (.name "self") "<sent>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 6)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 5)))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 11)))
                                        (.tryCatch
                                        (.seq
                                        (.assign
                                        "<yielded>"
                                        (.field
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "curr"))])
                                        "key"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 10)))
                                        (.seq
                                        (.setField (.name "self") "<handler>" (.lit (.int 5)))
                                        (.seq
                                        (.setField (.name "self") "<state>" (.lit (.int 1)))
                                        (.seq (.ret (.name "<yielded>")) .skip)))))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 5)))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 12)))
                                        (.tryCatch
                                        (.ifte
                                        (.binop
                                        "<"
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "time"))])
                                        (.field
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "curr"))])
                                        "expires"))
                                        (.setField (.name "self") "<pc>" (.lit (.int 11)))
                                        (.setField (.name "self") "<pc>" (.lit (.int 6))))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 5)))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 13)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "time"))
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "value_tmp0"))]))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 12)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 5)))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 14)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "value_tmp0"))
                                        (.mcall
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "manager_tmp0"))])
                                        "__enter__"
                                        []))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 13)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 15)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "exit_tmp0"))
                                        (.field
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "manager_tmp0"))])
                                        "__exit__"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 14)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 16)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "enter_tmp0"))
                                        (.field
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "manager_tmp0"))])
                                        "__enter__"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 15)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 17)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "manager_tmp0"))
                                        (.field
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "self"))])
                                        "timer"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 16)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 18)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "curr"))
                                        (.field
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "root"))])
                                        "next"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 1)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 19)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "root"))
                                        (.field
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "self"))])
                                        "_TTLCache__root"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 18)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int (-1))))
                                        (.seq
                                        (.setField (.name "self") "<state>" (.lit (.int 3)))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<return>")
                                        (.lit .unit))
                                        (.raise (.unop "py:exception:StopIteration" (.tupleE [])))
                                        (.hole "generator:return-value"))
                                        .skip))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int (-2))))
                                        (.seq
                                        (.setField (.name "self") "<state>" (.lit (.int 3)))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<exception>")
                                        (.lit (.str "StopIteration")))
                                        (.raise (.unop "py:exception:RuntimeError" (.tupleE [])))
                                        (.raise (.field (.name "self") "<exception>")))
                                        .skip))
                                        (.hole "generator:invalid-continuation")))))))))))))))))))))))
                      .skip)))))) }

/-- `<generator>.cachetools/__init__.py:<module>.TLRUCache.__iter__.<resume>`  (from ``) -/
def f__generator__cachetools___init___py__module__TLRUCache___iter____resume_ : Func :=
  { name := "<generator>.cachetools/__init__.py:<module>.TLRUCache.__iter__.<resume>"
  , params := ["self", "value"]
  , pythonSignature := some { positionalOnly := ["self", "value"], keywordOnly := [], required := ["self", "value"], isMethod := some false }
  , body := (.ifte
            (.binop "==" (.field (.name "self") "<state>") (.lit (.int 3)))
            (.raise (.unop "py:exception:StopIteration" (.tupleE [])))
            (.ifte
              (.binop "==" (.field (.name "self") "<state>") (.lit (.int 2)))
              (.raise (.unop "py:exception:ValueError" (.tupleE [])))
              (.ifte
                (.cond
                  (.binop "==" (.field (.name "self") "<state>") (.lit (.int 0)))
                  (.cond
                    (.binop "!=" (.name "value") (.lit .unit))
                    (.lit (.bool true))
                    (.lit (.bool false)))
                  (.lit (.bool false)))
                (.raise (.unop "py:exception:TypeError" (.tupleE [])))
                (.seq
                  (.setField (.name "self") "<sent>" (.name "value"))
                  (.seq
                    (.setField (.name "self") "<state>" (.lit (.int 2)))
                    (.seq
                      (.loop
                        (.lit (.bool true))
                        (.ifte
                          (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 1)))
                          (.tryCatch
                            (.seq
                              (.setIndex
                                (.field (.name "self") "<locals>")
                                (.lit (.str "curr"))
                                (.call
                                  "<python-next>"
                                  [ (.mcall
                                      (.name "self")
                                      "__read_local__"
                                      [(.lit (.str "<generator-temp>12"))]) ]))
                              (.seq (.setField (.name "self") "<pc>" (.lit (.int 22))) .skip))
                            "<caught>"
                            (.seq
                              (.setField (.name "self") "<exception>" (.name "<caught>"))
                              (.seq (.setField (.name "self") "<pc>" (.lit (.int 23))) .skip)))
                          (.ifte
                            (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 2)))
                            (.tryCatch
                              (.seq
                                (.setField
                                  (.name "self")
                                  "<exception>"
                                  (.mcall
                                    (.name "self")
                                    "__read_local__"
                                    [(.lit (.str "<generator-temp>13"))]))
                                (.seq (.setField (.name "self") "<pc>" (.lit (.int (-2)))) .skip))
                              "<caught>"
                              (.seq
                                (.setField (.name "self") "<exception>" (.name "<caught>"))
                                (.seq (.setField (.name "self") "<pc>" (.lit (.int (-2)))) .skip)))
                            (.ifte
                              (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 3)))
                              (.tryCatch
                                (.seq
                                  (.expr
                                    (.mcall
                                      (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "manager_tmp0"))])
                                      "__exit__"
                                      []))
                                  (.seq (.setField (.name "self") "<pc>" (.lit (.int 2))) .skip))
                                "<caught>"
                                (.seq
                                  (.setField (.name "self") "<exception>" (.name "<caught>"))
                                  (.seq (.setField (.name "self") "<pc>" (.lit (.int (-2)))) .skip)))
                              (.ifte
                                (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 4)))
                                (.tryCatch
                                  (.seq
                                    (.setIndex
                                      (.field (.name "self") "<locals>")
                                      (.lit (.str "<generator-temp>13"))
                                      (.field (.name "self") "<exception>"))
                                    (.seq (.setField (.name "self") "<pc>" (.lit (.int 3))) .skip))
                                  "<caught>"
                                  (.seq
                                    (.setField (.name "self") "<exception>" (.name "<caught>"))
                                    (.seq
                                      (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                      .skip)))
                                (.ifte
                                  (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 5)))
                                  (.tryCatch
                                    (.seq
                                      (.expr
                                        (.mcall
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "manager_tmp0"))])
                                        "__exit__"
                                        []))
                                      (.seq (.setField (.name "self") "<pc>" (.lit (.int 1))) .skip))
                                    "<caught>"
                                    (.seq
                                      (.setField (.name "self") "<exception>" (.name "<caught>"))
                                      (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                  (.ifte
                                    (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 6)))
                                    (.tryCatch
                                      (.seq
                                        (.expr
                                        (.mcall
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "manager_tmp0"))])
                                        "__exit__"
                                        []))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-1))))
                                        .skip))
                                      "<caught>"
                                      (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                    (.ifte
                                      (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 7)))
                                      (.tryCatch
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "manager_tmp0"))])
                                        "__exit__"
                                        []))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 1)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                      (.ifte
                                        (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 8)))
                                        (.tryCatch
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "manager_tmp0"))])
                                        "__exit__"
                                        []))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-1))))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                        (.ifte
                                        (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 9)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "$exprV$196"))
                                        (.field (.name "self") "<sent>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 5)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 4)))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 10)))
                                        (.tryCatch
                                        (.seq
                                        (.assign
                                        "<yielded>"
                                        (.field
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "curr"))])
                                        "key"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 9)))
                                        (.seq
                                        (.setField (.name "self") "<handler>" (.lit (.int 4)))
                                        (.seq
                                        (.setField (.name "self") "<state>" (.lit (.int 1)))
                                        (.seq (.ret (.name "<yielded>")) .skip)))))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 4)))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 11)))
                                        (.tryCatch
                                        (.ifte
                                        (.cond
                                        (.binop
                                        "=="
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "$exprV$195"))])
                                        (.lit (.int 0)))
                                        (.cond
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "$exprV$194"))])
                                        (.lit (.bool true))
                                        (.lit (.bool false)))
                                        (.binop
                                        "=="
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "$exprV$195"))])
                                        (.lit (.int 2))))
                                        (.setField (.name "self") "<pc>" (.lit (.int 10)))
                                        (.setField (.name "self") "<pc>" (.lit (.int 5))))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 4)))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 12)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "$exprV$195"))
                                        (.lit (.int 0)))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 11)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 4)))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 13)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "$exprV$194"))
                                        (.unop
                                        "!"
                                        (.field
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "curr"))])
                                        "removed")))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 12)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 4)))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 14)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "$exprV$195"))
                                        (.lit (.int 1)))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 11)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 4)))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 15)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "$exprV$194"))
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "$exprV$193"))]))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 14)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 4)))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 16)))
                                        (.tryCatch
                                        (.ifte
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "$exprV$193"))])
                                        (.setField (.name "self") "<pc>" (.lit (.int 13)))
                                        (.setField (.name "self") "<pc>" (.lit (.int 15))))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 4)))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 17)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "$exprV$193"))
                                        (.binop
                                        "<"
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "time"))])
                                        (.field
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "curr"))])
                                        "expires")))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 16)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 4)))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 18)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "time"))
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "value_tmp0"))]))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 17)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 4)))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 19)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "value_tmp0"))
                                        (.mcall
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "manager_tmp0"))])
                                        "__enter__"
                                        []))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 18)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 20)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "exit_tmp0"))
                                        (.field
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "manager_tmp0"))])
                                        "__exit__"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 19)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 21)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "enter_tmp0"))
                                        (.field
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "manager_tmp0"))])
                                        "__enter__"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 20)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 22)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "manager_tmp0"))
                                        (.field
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "self"))])
                                        "timer"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 21)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 23)))
                                        (.tryCatch
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<exception>")
                                        (.lit (.str "StopIteration")))
                                        (.setField (.name "self") "<pc>" (.lit (.int (-1))))
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2)))))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 24)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "<generator-temp>12"))
                                        (.call
                                        "<python-iter>"
                                        [ (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "tmp1"))]) ]))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 1)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int 25)))
                                        (.tryCatch
                                        (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "tmp1"))
                                        (.field
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "self"))])
                                        "_TLRUCache__order"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 24)))
                                        .skip))
                                        "<caught>"
                                        (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int (-1))))
                                        (.seq
                                        (.setField (.name "self") "<state>" (.lit (.int 3)))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<return>")
                                        (.lit .unit))
                                        (.raise (.unop "py:exception:StopIteration" (.tupleE [])))
                                        (.hole "generator:return-value"))
                                        .skip))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int (-2))))
                                        (.seq
                                        (.setField (.name "self") "<state>" (.lit (.int 3)))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<exception>")
                                        (.lit (.str "StopIteration")))
                                        (.raise (.unop "py:exception:RuntimeError" (.tupleE [])))
                                        (.raise (.field (.name "self") "<exception>")))
                                        .skip))
                                        (.hole "generator:invalid-continuation")))))))))))))))))))))))))))))
                      .skip)))))) }

/-- `<generator>.cachetools/keys.py:<module>.typedkey.<genexpr>0.<resume>`  (from ``) -/
def f__generator__cachetools_keys_py__module__typedkey__genexpr_0__resume_ : Func :=
  { name := "<generator>.cachetools/keys.py:<module>.typedkey.<genexpr>0.<resume>"
  , params := ["self", "value"]
  , pythonSignature := some { positionalOnly := ["self", "value"], keywordOnly := [], required := ["self", "value"], isMethod := some false }
  , body := (.ifte
            (.binop "==" (.field (.name "self") "<state>") (.lit (.int 3)))
            (.raise (.unop "py:exception:StopIteration" (.tupleE [])))
            (.ifte
              (.binop "==" (.field (.name "self") "<state>") (.lit (.int 2)))
              (.raise (.unop "py:exception:ValueError" (.tupleE [])))
              (.ifte
                (.cond
                  (.binop "==" (.field (.name "self") "<state>") (.lit (.int 0)))
                  (.cond
                    (.binop "!=" (.name "value") (.lit .unit))
                    (.lit (.bool true))
                    (.lit (.bool false)))
                  (.lit (.bool false)))
                (.raise (.unop "py:exception:TypeError" (.tupleE [])))
                (.seq
                  (.setField (.name "self") "<sent>" (.name "value"))
                  (.seq
                    (.setField (.name "self") "<state>" (.lit (.int 2)))
                    (.seq
                      (.loop
                        (.lit (.bool true))
                        (.ifte
                          (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 1)))
                          (.tryCatch
                            (.seq
                              (.setIndex
                                (.field (.name "self") "<locals>")
                                (.lit (.str "$comp$tmp2"))
                                (.call
                                  "<python-next>"
                                  [ (.mcall
                                      (.name "self")
                                      "__read_local__"
                                      [(.lit (.str "<generator-temp>7"))]) ]))
                              (.seq (.setField (.name "self") "<pc>" (.lit (.int 4))) .skip))
                            "<caught>"
                            (.seq
                              (.setField (.name "self") "<exception>" (.name "<caught>"))
                              (.seq (.setField (.name "self") "<pc>" (.lit (.int 5))) .skip)))
                          (.ifte
                            (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 2)))
                            (.tryCatch
                              (.seq
                                (.assign
                                  "<yielded>"
                                  (.call
                                    "type"
                                    [ (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "$comp$v"))]) ]))
                                (.seq
                                  (.setField (.name "self") "<pc>" (.lit (.int 1)))
                                  (.seq
                                    (.setField (.name "self") "<handler>" (.lit (.int (-2))))
                                    (.seq
                                      (.setField (.name "self") "<state>" (.lit (.int 1)))
                                      (.seq (.ret (.name "<yielded>")) .skip)))))
                              "<caught>"
                              (.seq
                                (.setField (.name "self") "<exception>" (.name "<caught>"))
                                (.seq (.setField (.name "self") "<pc>" (.lit (.int (-2)))) .skip)))
                            (.ifte
                              (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 3)))
                              (.tryCatch
                                (.seq
                                  (.setIndex
                                    (.field (.name "self") "<locals>")
                                    (.lit (.str "$comp$v"))
                                    (.index
                                      (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "$comp$tmp2"))])
                                      (.lit (.int 1))))
                                  (.seq (.setField (.name "self") "<pc>" (.lit (.int 2))) .skip))
                                "<caught>"
                                (.seq
                                  (.setField (.name "self") "<exception>" (.name "<caught>"))
                                  (.seq (.setField (.name "self") "<pc>" (.lit (.int (-2)))) .skip)))
                              (.ifte
                                (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 4)))
                                (.tryCatch
                                  (.seq
                                    (.setIndex
                                      (.field (.name "self") "<locals>")
                                      (.lit (.str "$comp$_"))
                                      (.index
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "$comp$tmp2"))])
                                        (.lit (.int 0))))
                                    (.seq (.setField (.name "self") "<pc>" (.lit (.int 3))) .skip))
                                  "<caught>"
                                  (.seq
                                    (.setField (.name "self") "<exception>" (.name "<caught>"))
                                    (.seq
                                      (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                      .skip)))
                                (.ifte
                                  (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 5)))
                                  (.tryCatch
                                    (.ifte
                                      (.binop
                                        "=="
                                        (.field (.name "self") "<exception>")
                                        (.lit (.str "StopIteration")))
                                      (.setField (.name "self") "<pc>" (.lit (.int (-1))))
                                      (.setField (.name "self") "<pc>" (.lit (.int (-2)))))
                                    "<caught>"
                                    (.seq
                                      (.setField (.name "self") "<exception>" (.name "<caught>"))
                                      (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                  (.ifte
                                    (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 6)))
                                    (.tryCatch
                                      (.seq
                                        (.setIndex
                                        (.field (.name "self") "<locals>")
                                        (.lit (.str "<generator-temp>7"))
                                        (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "<genexpr-iterator>"))]))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int 1)))
                                        .skip))
                                      "<caught>"
                                      (.seq
                                        (.setField (.name "self") "<exception>" (.name "<caught>"))
                                        (.seq
                                        (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                        .skip)))
                                    (.ifte
                                      (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int (-1))))
                                      (.seq
                                        (.setField (.name "self") "<state>" (.lit (.int 3)))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<return>")
                                        (.lit .unit))
                                        (.raise (.unop "py:exception:StopIteration" (.tupleE [])))
                                        (.hole "generator:return-value"))
                                        .skip))
                                      (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<pc>")
                                        (.lit (.int (-2))))
                                        (.seq
                                        (.setField (.name "self") "<state>" (.lit (.int 3)))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<exception>")
                                        (.lit (.str "StopIteration")))
                                        (.raise (.unop "py:exception:RuntimeError" (.tupleE [])))
                                        (.raise (.field (.name "self") "<exception>")))
                                        .skip))
                                        (.hole "generator:invalid-continuation"))))))))))
                      .skip)))))) }

/-- `cachetools/keys.py:<module>.typedkey.<genexpr>0`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module__typedkey__genexpr_0 : Func :=
  { name := "cachetools/keys.py:<module>.typedkey.<genexpr>0"
  , params := ["<genexpr-iterator>"]
  , analysisBody := some (.forIn
            "$comp$tmp2"
            (.name "<genexpr-iterator>")
            (.seq
              (.assign "$comp$_" (.index (.name "$comp$tmp2") (.lit (.int 0))))
              (.seq
                (.assign "$comp$v" (.index (.name "$comp$tmp2") (.lit (.int 1))))
                (.expr (.call "type" [(.name "$comp$v")])))))
  , pythonSignature := some { positionalOnly := ["<genexpr-iterator>"], keywordOnly := [], required := ["<genexpr-iterator>"], isMethod := some false }
  , body := (.seq
            (.assign "<generator-frame>" (.alloc "<generator>" []))
            (.seq
              (.setField
                (.name "<generator-frame>")
                "<locals>"
                (.dictE [((.lit (.str "<genexpr-iterator>")), (.name "<genexpr-iterator>"))]))
              (.seq
                (.setField
                  (.name "<generator-frame>")
                  "<resume>"
                  (.fnref "<generator>.cachetools/keys.py:<module>.typedkey.<genexpr>0.<resume>"))
                (.seq
                  (.setField (.name "<generator-frame>") "<pc>" (.lit (.int 6)))
                  (.seq
                    (.setField (.name "<generator-frame>") "<state>" (.lit (.int 0)))
                    (.seq
                      (.setField (.name "<generator-frame>") "<return>" (.lit .unit))
                      (.seq (.ret (.name "<generator-frame>")) .skip))))))) }

/-- `<generator>.cachetools/keys.py:<module>.typedkey.<genexpr>9.<resume>`  (from ``) -/
def f__generator__cachetools_keys_py__module__typedkey__genexpr_9__resume_ : Func :=
  { name := "<generator>.cachetools/keys.py:<module>.typedkey.<genexpr>9.<resume>"
  , params := ["self", "value"]
  , pythonSignature := some { positionalOnly := ["self", "value"], keywordOnly := [], required := ["self", "value"], isMethod := some false }
  , body := (.ifte
            (.binop "==" (.field (.name "self") "<state>") (.lit (.int 3)))
            (.raise (.unop "py:exception:StopIteration" (.tupleE [])))
            (.ifte
              (.binop "==" (.field (.name "self") "<state>") (.lit (.int 2)))
              (.raise (.unop "py:exception:ValueError" (.tupleE [])))
              (.ifte
                (.cond
                  (.binop "==" (.field (.name "self") "<state>") (.lit (.int 0)))
                  (.cond
                    (.binop "!=" (.name "value") (.lit .unit))
                    (.lit (.bool true))
                    (.lit (.bool false)))
                  (.lit (.bool false)))
                (.raise (.unop "py:exception:TypeError" (.tupleE [])))
                (.seq
                  (.setField (.name "self") "<sent>" (.name "value"))
                  (.seq
                    (.setField (.name "self") "<state>" (.lit (.int 2)))
                    (.seq
                      (.loop
                        (.lit (.bool true))
                        (.ifte
                          (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 1)))
                          (.tryCatch
                            (.seq
                              (.setIndex
                                (.field (.name "self") "<locals>")
                                (.lit (.str "$comp$v"))
                                (.call
                                  "<python-next>"
                                  [ (.mcall
                                      (.name "self")
                                      "__read_local__"
                                      [(.lit (.str "<generator-temp>4"))]) ]))
                              (.seq (.setField (.name "self") "<pc>" (.lit (.int 2))) .skip))
                            "<caught>"
                            (.seq
                              (.setField (.name "self") "<exception>" (.name "<caught>"))
                              (.seq (.setField (.name "self") "<pc>" (.lit (.int 3))) .skip)))
                          (.ifte
                            (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 2)))
                            (.tryCatch
                              (.seq
                                (.assign
                                  "<yielded>"
                                  (.call
                                    "type"
                                    [ (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "$comp$v"))]) ]))
                                (.seq
                                  (.setField (.name "self") "<pc>" (.lit (.int 1)))
                                  (.seq
                                    (.setField (.name "self") "<handler>" (.lit (.int (-2))))
                                    (.seq
                                      (.setField (.name "self") "<state>" (.lit (.int 1)))
                                      (.seq (.ret (.name "<yielded>")) .skip)))))
                              "<caught>"
                              (.seq
                                (.setField (.name "self") "<exception>" (.name "<caught>"))
                                (.seq (.setField (.name "self") "<pc>" (.lit (.int (-2)))) .skip)))
                            (.ifte
                              (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 3)))
                              (.tryCatch
                                (.ifte
                                  (.binop
                                    "=="
                                    (.field (.name "self") "<exception>")
                                    (.lit (.str "StopIteration")))
                                  (.setField (.name "self") "<pc>" (.lit (.int (-1))))
                                  (.setField (.name "self") "<pc>" (.lit (.int (-2)))))
                                "<caught>"
                                (.seq
                                  (.setField (.name "self") "<exception>" (.name "<caught>"))
                                  (.seq (.setField (.name "self") "<pc>" (.lit (.int (-2)))) .skip)))
                              (.ifte
                                (.binop "==" (.field (.name "self") "<pc>") (.lit (.int 4)))
                                (.tryCatch
                                  (.seq
                                    (.setIndex
                                      (.field (.name "self") "<locals>")
                                      (.lit (.str "<generator-temp>4"))
                                      (.mcall
                                        (.name "self")
                                        "__read_local__"
                                        [(.lit (.str "<genexpr-iterator>"))]))
                                    (.seq (.setField (.name "self") "<pc>" (.lit (.int 1))) .skip))
                                  "<caught>"
                                  (.seq
                                    (.setField (.name "self") "<exception>" (.name "<caught>"))
                                    (.seq
                                      (.setField (.name "self") "<pc>" (.lit (.int (-2))))
                                      .skip)))
                                (.ifte
                                  (.binop "==" (.field (.name "self") "<pc>") (.lit (.int (-1))))
                                  (.seq
                                    (.setField (.name "self") "<state>" (.lit (.int 3)))
                                    (.seq
                                      (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<return>")
                                        (.lit .unit))
                                        (.raise (.unop "py:exception:StopIteration" (.tupleE [])))
                                        (.hole "generator:return-value"))
                                      .skip))
                                  (.ifte
                                    (.binop "==" (.field (.name "self") "<pc>") (.lit (.int (-2))))
                                    (.seq
                                      (.setField (.name "self") "<state>" (.lit (.int 3)))
                                      (.seq
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.field (.name "self") "<exception>")
                                        (.lit (.str "StopIteration")))
                                        (.raise (.unop "py:exception:RuntimeError" (.tupleE [])))
                                        (.raise (.field (.name "self") "<exception>")))
                                        .skip))
                                    (.hole "generator:invalid-continuation"))))))))
                      .skip)))))) }

/-- `cachetools/keys.py:<module>.typedkey.<genexpr>9`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module__typedkey__genexpr_9 : Func :=
  { name := "cachetools/keys.py:<module>.typedkey.<genexpr>9"
  , params := ["<genexpr-iterator>"]
  , analysisBody := some (.forIn "$comp$v" (.name "<genexpr-iterator>") (.expr (.call "type" [(.name "$comp$v")])))
  , pythonSignature := some { positionalOnly := ["<genexpr-iterator>"], keywordOnly := [], required := ["<genexpr-iterator>"], isMethod := some false }
  , body := (.seq
            (.assign "<generator-frame>" (.alloc "<generator>" []))
            (.seq
              (.setField
                (.name "<generator-frame>")
                "<locals>"
                (.dictE [((.lit (.str "<genexpr-iterator>")), (.name "<genexpr-iterator>"))]))
              (.seq
                (.setField
                  (.name "<generator-frame>")
                  "<resume>"
                  (.fnref "<generator>.cachetools/keys.py:<module>.typedkey.<genexpr>9.<resume>"))
                (.seq
                  (.setField (.name "<generator-frame>") "<pc>" (.lit (.int 4)))
                  (.seq
                    (.setField (.name "<generator-frame>") "<state>" (.lit (.int 0)))
                    (.seq
                      (.setField (.name "<generator-frame>") "<return>" (.lit .unit))
                      (.seq (.ret (.name "<generator-frame>")) .skip))))))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := [f__module_objects___module_, f_cachetools__cached_py__module_, f_cachetools__cachedmethod_py__module_, f_cachetools___init___py__module_, f_cachetools_func_py__module_, f_cachetools_keys_py__module_]

/-- Source dialect: `.python` (integer division/modulo convention).

`classDecls` records qualified class namespaces and ordered bases;
unresolved ancestry remains an explicit lookup boundary.
`builtinBases` lists the classes whose base is a builtin type, so that
`Expr.alloc` builds a `Val.bobj` and not an opaque `Val.ref`.
`properties` lists every `@property` as `(class, name)`, so that an
attribute read of one runs the getter instead of missing the field. -/
def program : Program := { dialect := .python, auxiliaryFuncs := [f__autoform___generator____init__, f__autoform___generator____iter__, f__autoform___generator____read_local__, f__autoform___generator____next__, f__autoform___generator__send, f__autoform___generator__close, f__autoform___generator__throw, f__generator__cachetools___init___py__module__TTLCache___iter____resume_, f__generator__cachetools___init___py__module__TLRUCache___iter____resume_, f__generator__cachetools_keys_py__module__typedkey__genexpr_0__resume_, f_cachetools_keys_py__module__typedkey__genexpr_0, f__generator__cachetools_keys_py__module__typedkey__genexpr_9__resume_, f_cachetools_keys_py__module__typedkey__genexpr_9], classDecls := [{ name := "cachetools/__init__.py:<module>.Cache", shortName := "Cache", bases := ["<external>collections.abc.MutableMapping"], attributes := [("_Cache__marker", .stored "<classattr>cachetools/__init__.py:<module>.Cache._Cache__marker"), ("_Cache__size", .opaque "class-attribute:unmodeled-value"), ("__init__", .method "cachetools/__init__.py:<module>.Cache.__init__"), ("__repr__", .method "cachetools/__init__.py:<module>.Cache.__repr__"), ("__getitem__", .method "cachetools/__init__.py:<module>.Cache.__getitem__"), ("__setitem__", .method "cachetools/__init__.py:<module>.Cache.__setitem__"), ("__delitem__", .method "cachetools/__init__.py:<module>.Cache.__delitem__"), ("__contains__", .method "cachetools/__init__.py:<module>.Cache.__contains__"), ("__missing__", .method "cachetools/__init__.py:<module>.Cache.__missing__"), ("__iter__", .method "cachetools/__init__.py:<module>.Cache.__iter__"), ("__len__", .method "cachetools/__init__.py:<module>.Cache.__len__"), ("get", .method "cachetools/__init__.py:<module>.Cache.get"), ("pop", .method "cachetools/__init__.py:<module>.Cache.pop"), ("setdefault", .method "cachetools/__init__.py:<module>.Cache.setdefault"), ("clear", .method "cachetools/__init__.py:<module>.Cache.clear"), ("maxsize", .property "cachetools/__init__.py:<module>.Cache.maxsize"), ("currsize", .property "cachetools/__init__.py:<module>.Cache.currsize"), ("getsizeof", .method "cachetools/__init__.py:<module>.Cache.getsizeof")] }, { name := "cachetools/__init__.py:<module>.FIFOCache", shortName := "FIFOCache", bases := ["cachetools/__init__.py:<module>.Cache"], attributes := [("__init__", .method "cachetools/__init__.py:<module>.FIFOCache.__init__"), ("__setitem__", .method "cachetools/__init__.py:<module>.FIFOCache.__setitem__"), ("__delitem__", .method "cachetools/__init__.py:<module>.FIFOCache.__delitem__"), ("popitem", .method "cachetools/__init__.py:<module>.FIFOCache.popitem"), ("clear", .method "cachetools/__init__.py:<module>.FIFOCache.clear")] }, { name := "cachetools/__init__.py:<module>.LFUCache", shortName := "LFUCache", bases := ["cachetools/__init__.py:<module>.Cache"], attributes := [("_Link", .opaque "class-attribute:nested-class"), ("__init__", .method "cachetools/__init__.py:<module>.LFUCache.__init__"), ("__getitem__", .method "cachetools/__init__.py:<module>.LFUCache.__getitem__"), ("__setitem__", .method "cachetools/__init__.py:<module>.LFUCache.__setitem__"), ("__delitem__", .method "cachetools/__init__.py:<module>.LFUCache.__delitem__"), ("popitem", .method "cachetools/__init__.py:<module>.LFUCache.popitem"), ("clear", .method "cachetools/__init__.py:<module>.LFUCache.clear"), ("_LFUCache__touch", .method "cachetools/__init__.py:<module>.LFUCache._LFUCache__touch")] }, { name := "cachetools/__init__.py:<module>.LFUCache._Link", shortName := "_Link", bases := [], attributes := [("__slots__", .opaque "class-attribute:unmodeled-value"), ("__init__", .method "cachetools/__init__.py:<module>.LFUCache._Link.__init__"), ("unlink", .method "cachetools/__init__.py:<module>.LFUCache._Link.unlink"), ("count", .slot "<slot>cachetools/__init__.py:<module>.LFUCache._Link.count"), ("keys", .slot "<slot>cachetools/__init__.py:<module>.LFUCache._Link.keys"), ("next", .slot "<slot>cachetools/__init__.py:<module>.LFUCache._Link.next"), ("prev", .slot "<slot>cachetools/__init__.py:<module>.LFUCache._Link.prev")], slots := some ["count", "keys", "next", "prev"] }, { name := "cachetools/__init__.py:<module>.LRUCache", shortName := "LRUCache", bases := ["cachetools/__init__.py:<module>.Cache"], attributes := [("__init__", .method "cachetools/__init__.py:<module>.LRUCache.__init__"), ("__getitem__", .method "cachetools/__init__.py:<module>.LRUCache.__getitem__"), ("__setitem__", .method "cachetools/__init__.py:<module>.LRUCache.__setitem__"), ("__delitem__", .method "cachetools/__init__.py:<module>.LRUCache.__delitem__"), ("popitem", .method "cachetools/__init__.py:<module>.LRUCache.popitem"), ("clear", .method "cachetools/__init__.py:<module>.LRUCache.clear"), ("_LRUCache__touch", .method "cachetools/__init__.py:<module>.LRUCache._LRUCache__touch")] }, { name := "cachetools/__init__.py:<module>.RRCache", shortName := "RRCache", bases := ["cachetools/__init__.py:<module>.Cache"], attributes := [("__init__", .method "cachetools/__init__.py:<module>.RRCache.__init__"), ("choice", .property "cachetools/__init__.py:<module>.RRCache.choice"), ("__setitem__", .method "cachetools/__init__.py:<module>.RRCache.__setitem__"), ("__delitem__", .method "cachetools/__init__.py:<module>.RRCache.__delitem__"), ("popitem", .method "cachetools/__init__.py:<module>.RRCache.popitem"), ("clear", .method "cachetools/__init__.py:<module>.RRCache.clear")] }, { name := "cachetools/__init__.py:<module>.TLRUCache", shortName := "TLRUCache", bases := ["cachetools/__init__.py:<module>._TimedCache"], attributes := [("_TLRUCache__HEAP_CLEANUP_FACTOR", .opaque "class-attribute:unmodeled-value"), ("_Item", .opaque "class-attribute:nested-class"), ("__init__", .method "cachetools/__init__.py:<module>.TLRUCache.__init__"), ("__contains__", .method "cachetools/__init__.py:<module>.TLRUCache.__contains__"), ("__getitem__", .method "cachetools/__init__.py:<module>.TLRUCache.__getitem__"), ("__setitem__", .method "cachetools/__init__.py:<module>.TLRUCache.__setitem__"), ("__delitem__", .method "cachetools/__init__.py:<module>.TLRUCache.__delitem__"), ("__iter__", .method "cachetools/__init__.py:<module>.TLRUCache.__iter__"), ("ttu", .property "cachetools/__init__.py:<module>.TLRUCache.ttu"), ("expire", .method "cachetools/__init__.py:<module>.TLRUCache.expire"), ("popitem", .method "cachetools/__init__.py:<module>.TLRUCache.popitem"), ("clear", .method "cachetools/__init__.py:<module>.TLRUCache.clear"), ("_TLRUCache__getitem", .method "cachetools/__init__.py:<module>.TLRUCache._TLRUCache__getitem"), ("_TLRUCache__delitem", .method "cachetools/__init__.py:<module>.TLRUCache._TLRUCache__delitem")] }, { name := "cachetools/__init__.py:<module>.TLRUCache._Item", shortName := "_Item", bases := [], attributes := [("__slots__", .opaque "class-attribute:unmodeled-value"), ("__init__", .method "cachetools/__init__.py:<module>.TLRUCache._Item.__init__"), ("__lt__", .method "cachetools/__init__.py:<module>.TLRUCache._Item.__lt__"), ("expires", .slot "<slot>cachetools/__init__.py:<module>.TLRUCache._Item.expires"), ("key", .slot "<slot>cachetools/__init__.py:<module>.TLRUCache._Item.key"), ("removed", .slot "<slot>cachetools/__init__.py:<module>.TLRUCache._Item.removed")], slots := some ["expires", "key", "removed"], definitionBarrier := some "class-definition:decorator-or-metaclass" }, { name := "cachetools/__init__.py:<module>.TTLCache", shortName := "TTLCache", bases := ["cachetools/__init__.py:<module>._TimedCache"], attributes := [("_Link", .opaque "class-attribute:nested-class"), ("__init__", .method "cachetools/__init__.py:<module>.TTLCache.__init__"), ("__contains__", .method "cachetools/__init__.py:<module>.TTLCache.__contains__"), ("__getitem__", .method "cachetools/__init__.py:<module>.TTLCache.__getitem__"), ("__setitem__", .method "cachetools/__init__.py:<module>.TTLCache.__setitem__"), ("__delitem__", .method "cachetools/__init__.py:<module>.TTLCache.__delitem__"), ("__iter__", .method "cachetools/__init__.py:<module>.TTLCache.__iter__"), ("__setstate__", .method "cachetools/__init__.py:<module>.TTLCache.__setstate__"), ("ttl", .property "cachetools/__init__.py:<module>.TTLCache.ttl"), ("expire", .method "cachetools/__init__.py:<module>.TTLCache.expire"), ("popitem", .method "cachetools/__init__.py:<module>.TTLCache.popitem"), ("clear", .method "cachetools/__init__.py:<module>.TTLCache.clear"), ("_TTLCache__getlink", .method "cachetools/__init__.py:<module>.TTLCache._TTLCache__getlink")] }, { name := "cachetools/__init__.py:<module>.TTLCache._Link", shortName := "_Link", bases := [], attributes := [("__slots__", .opaque "class-attribute:unmodeled-value"), ("__init__", .method "cachetools/__init__.py:<module>.TTLCache._Link.__init__"), ("__reduce__", .method "cachetools/__init__.py:<module>.TTLCache._Link.__reduce__"), ("unlink", .method "cachetools/__init__.py:<module>.TTLCache._Link.unlink"), ("expires", .slot "<slot>cachetools/__init__.py:<module>.TTLCache._Link.expires"), ("key", .slot "<slot>cachetools/__init__.py:<module>.TTLCache._Link.key"), ("next", .slot "<slot>cachetools/__init__.py:<module>.TTLCache._Link.next"), ("prev", .slot "<slot>cachetools/__init__.py:<module>.TTLCache._Link.prev")], slots := some ["expires", "key", "next", "prev"] }, { name := "cachetools/__init__.py:<module>._DefaultSize", shortName := "_DefaultSize", bases := [], attributes := [("__slots__", .opaque "class-attribute:unmodeled-value"), ("__getitem__", .method "cachetools/__init__.py:<module>._DefaultSize.__getitem__"), ("__setitem__", .method "cachetools/__init__.py:<module>._DefaultSize.__setitem__"), ("pop", .method "cachetools/__init__.py:<module>._DefaultSize.pop"), ("clear", .method "cachetools/__init__.py:<module>._DefaultSize.clear")], slots := some [] }, { name := "cachetools/__init__.py:<module>._TimedCache", shortName := "_TimedCache", bases := ["cachetools/__init__.py:<module>.Cache"], attributes := [("_Timer", .opaque "class-attribute:nested-class"), ("__init__", .method "cachetools/__init__.py:<module>._TimedCache.__init__"), ("__repr__", .method "cachetools/__init__.py:<module>._TimedCache.__repr__"), ("__len__", .method "cachetools/__init__.py:<module>._TimedCache.__len__"), ("currsize", .property "cachetools/__init__.py:<module>._TimedCache.currsize"), ("timer", .property "cachetools/__init__.py:<module>._TimedCache.timer"), ("get", .method "cachetools/__init__.py:<module>._TimedCache.get"), ("pop", .method "cachetools/__init__.py:<module>._TimedCache.pop"), ("setdefault", .method "cachetools/__init__.py:<module>._TimedCache.setdefault"), ("clear", .method "cachetools/__init__.py:<module>._TimedCache.clear"), ("expire", .method "cachetools/__init__.py:<module>._TimedCache.expire")] }, { name := "cachetools/__init__.py:<module>._TimedCache._Timer", shortName := "_Timer", bases := [], attributes := [("__init__", .method "cachetools/__init__.py:<module>._TimedCache._Timer.__init__"), ("__call__", .method "cachetools/__init__.py:<module>._TimedCache._Timer.__call__"), ("__enter__", .method "cachetools/__init__.py:<module>._TimedCache._Timer.__enter__"), ("__exit__", .method "cachetools/__init__.py:<module>._TimedCache._Timer.__exit__"), ("__reduce__", .method "cachetools/__init__.py:<module>._TimedCache._Timer.__reduce__"), ("__getattr__", .method "cachetools/__init__.py:<module>._TimedCache._Timer.__getattr__")] }, { name := "cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase", shortName := "_DeprecatedDescriptorBase", bases := ["cachetools/_cachedmethod.py:<module>._DescriptorBase"], attributes := [("__init__", .method "cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase.__init__"), ("__call__", .method "cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase.__call__"), ("cache_clear", .method "cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase.cache_clear")] }, { name := "cachetools/_cachedmethod.py:<module>._DescriptorBase", shortName := "_DescriptorBase", bases := [], attributes := [("__init__", .method "cachetools/_cachedmethod.py:<module>._DescriptorBase.__init__"), ("__set_name__", .method "cachetools/_cachedmethod.py:<module>._DescriptorBase.__set_name__"), ("__get__", .method "cachetools/_cachedmethod.py:<module>._DescriptorBase.__get__")], definitionBarrier := some "class-definition:custom-class-hook" }, { name := "cachetools/_cachedmethod.py:<module>._WrapperBase", shortName := "_WrapperBase", bases := [], attributes := [("__init__", .method "cachetools/_cachedmethod.py:<module>._WrapperBase.__init__"), ("__call__", .method "cachetools/_cachedmethod.py:<module>._WrapperBase.__call__"), ("cache_clear", .method "cachetools/_cachedmethod.py:<module>._WrapperBase.cache_clear"), ("cache", .property "cachetools/_cachedmethod.py:<module>._WrapperBase.cache"), ("cache_key", .property "cachetools/_cachedmethod.py:<module>._WrapperBase.cache_key"), ("cache_lock", .property "cachetools/_cachedmethod.py:<module>._WrapperBase.cache_lock"), ("cache_condition", .property "cachetools/_cachedmethod.py:<module>._WrapperBase.cache_condition")] }, { name := "cachetools/_cachedmethod.py:<module>._condition.Descriptor", shortName := "Descriptor", bases := ["cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase"], attributes := [("Wrapper", .opaque "class-attribute:nested-class")], inheritanceBarrier := some "class-hierarchy:local-base-captures" }, { name := "cachetools/_cachedmethod.py:<module>._condition.Descriptor.Wrapper", shortName := "Wrapper", bases := ["cachetools/_cachedmethod.py:<module>._WrapperBase"], attributes := [("__init__", .method "cachetools/_cachedmethod.py:<module>._condition.Descriptor.Wrapper.__init__"), ("__call__", .method "cachetools/_cachedmethod.py:<module>._condition.Descriptor.Wrapper.__call__"), ("cache_clear", .method "cachetools/_cachedmethod.py:<module>._condition.Descriptor.Wrapper.cache_clear")], inheritanceBarrier := some "class-hierarchy:local-base-captures" }, { name := "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor", shortName := "Descriptor", bases := ["cachetools/_cachedmethod.py:<module>._DescriptorBase"], attributes := [("Wrapper", .opaque "class-attribute:nested-class")], inheritanceBarrier := some "class-hierarchy:local-base-captures" }, { name := "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper", shortName := "Wrapper", bases := ["cachetools/_cachedmethod.py:<module>._WrapperBase"], attributes := [("__init__", .method "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.__init__"), ("__call__", .method "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.__call__"), ("cache_clear", .method "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.cache_clear"), ("cache_info", .method "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.cache_info")], inheritanceBarrier := some "class-hierarchy:local-base-captures" }, { name := "cachetools/_cachedmethod.py:<module>._locked.Descriptor", shortName := "Descriptor", bases := ["cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase"], attributes := [("Wrapper", .opaque "class-attribute:nested-class")], inheritanceBarrier := some "class-hierarchy:local-base-captures" }, { name := "cachetools/_cachedmethod.py:<module>._locked.Descriptor.Wrapper", shortName := "Wrapper", bases := ["cachetools/_cachedmethod.py:<module>._WrapperBase"], attributes := [("__init__", .method "cachetools/_cachedmethod.py:<module>._locked.Descriptor.Wrapper.__init__"), ("__call__", .method "cachetools/_cachedmethod.py:<module>._locked.Descriptor.Wrapper.__call__"), ("cache_clear", .method "cachetools/_cachedmethod.py:<module>._locked.Descriptor.Wrapper.cache_clear")], inheritanceBarrier := some "class-hierarchy:local-base-captures" }, { name := "cachetools/_cachedmethod.py:<module>._locked_info.Descriptor", shortName := "Descriptor", bases := ["cachetools/_cachedmethod.py:<module>._DescriptorBase"], attributes := [("Wrapper", .opaque "class-attribute:nested-class")], inheritanceBarrier := some "class-hierarchy:local-base-captures" }, { name := "cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper", shortName := "Wrapper", bases := ["cachetools/_cachedmethod.py:<module>._WrapperBase"], attributes := [("__init__", .method "cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.__init__"), ("__call__", .method "cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.__call__"), ("cache_clear", .method "cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.cache_clear"), ("cache_info", .method "cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.cache_info")], inheritanceBarrier := some "class-hierarchy:local-base-captures" }, { name := "cachetools/_cachedmethod.py:<module>._unlocked.Descriptor", shortName := "Descriptor", bases := ["cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase"], attributes := [("Wrapper", .opaque "class-attribute:nested-class")], inheritanceBarrier := some "class-hierarchy:local-base-captures" }, { name := "cachetools/_cachedmethod.py:<module>._unlocked.Descriptor.Wrapper", shortName := "Wrapper", bases := ["cachetools/_cachedmethod.py:<module>._WrapperBase"], attributes := [("__init__", .method "cachetools/_cachedmethod.py:<module>._unlocked.Descriptor.Wrapper.__init__"), ("__call__", .method "cachetools/_cachedmethod.py:<module>._unlocked.Descriptor.Wrapper.__call__"), ("cache_clear", .method "cachetools/_cachedmethod.py:<module>._unlocked.Descriptor.Wrapper.cache_clear")], inheritanceBarrier := some "class-hierarchy:local-base-captures" }, { name := "cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor", shortName := "Descriptor", bases := ["cachetools/_cachedmethod.py:<module>._DescriptorBase"], attributes := [("Wrapper", .opaque "class-attribute:nested-class")], inheritanceBarrier := some "class-hierarchy:local-base-captures" }, { name := "cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper", shortName := "Wrapper", bases := ["cachetools/_cachedmethod.py:<module>._WrapperBase"], attributes := [("__init__", .method "cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.__init__"), ("__call__", .method "cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.__call__"), ("cache_clear", .method "cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.cache_clear"), ("cache_info", .method "cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.cache_info")], inheritanceBarrier := some "class-hierarchy:local-base-captures" }, { name := "cachetools/func.py:<module>._UnboundTTLCache", shortName := "_UnboundTTLCache", bases := ["cachetools/__init__.py:<module>.TTLCache"], attributes := [("__init__", .method "cachetools/func.py:<module>._UnboundTTLCache.__init__"), ("maxsize", .property "cachetools/func.py:<module>._UnboundTTLCache.maxsize")] }, { name := "cachetools/keys.py:<module>._HashedTuple", shortName := "_HashedTuple", bases := ["<unresolved-base>cachetools/keys.py:<module>._HashedTuple:0"], attributes := [("_HashedTuple__hashvalue", .opaque "class-attribute:unmodeled-value"), ("__hash__", .method "cachetools/keys.py:<module>._HashedTuple.__hash__"), ("__add__", .method "cachetools/keys.py:<module>._HashedTuple.__add__"), ("__radd__", .method "cachetools/keys.py:<module>._HashedTuple.__radd__"), ("__getstate__", .method "cachetools/keys.py:<module>._HashedTuple.__getstate__")] }], builtinBases := [("_HashedTuple", .tuple), ("cachetools/keys.py:<module>._HashedTuple", .tuple)], properties := [("Cache", "currsize"), ("Cache", "maxsize"), ("RRCache", "choice"), ("TLRUCache", "ttu"), ("TTLCache", "ttl"), ("_TimedCache", "currsize"), ("_TimedCache", "timer"), ("_UnboundTTLCache", "maxsize"), ("_WrapperBase", "cache"), ("_WrapperBase", "cache_condition"), ("_WrapperBase", "cache_key"), ("_WrapperBase", "cache_lock")], funcs := [
  f_cachetools___init___py__module___DefaultSize___getitem__,
  f_cachetools___init___py__module___DefaultSize___setitem__,
  f_cachetools___init___py__module___DefaultSize_pop,
  f_cachetools___init___py__module___DefaultSize_clear,
  f_cachetools___init___py__module__Cache___init__,
  f_cachetools___init___py__module__Cache___repr__,
  f_cachetools___init___py__module__Cache___getitem__,
  f_cachetools___init___py__module__Cache___setitem__,
  f_cachetools___init___py__module__Cache___delitem__,
  f_cachetools___init___py__module__Cache___contains__,
  f_cachetools___init___py__module__Cache___missing__,
  f_cachetools___init___py__module__Cache___iter__,
  f_cachetools___init___py__module__Cache___len__,
  f_cachetools___init___py__module__Cache_get,
  f_cachetools___init___py__module__Cache_pop,
  f_cachetools___init___py__module__Cache_setdefault,
  f_cachetools___init___py__module__Cache_clear,
  f_cachetools___init___py__module__Cache_maxsize,
  f_cachetools___init___py__module__Cache_currsize,
  f_cachetools___init___py__module__Cache_getsizeof,
  f_cachetools___init___py__module__FIFOCache___init__,
  f_cachetools___init___py__module__FIFOCache___setitem__,
  f_cachetools___init___py__module__FIFOCache___delitem__,
  f_cachetools___init___py__module__FIFOCache_popitem,
  f_cachetools___init___py__module__FIFOCache_clear,
  f_cachetools___init___py__module__LFUCache__Link___init__,
  f_cachetools___init___py__module__LFUCache__Link_unlink,
  f_cachetools___init___py__module__LFUCache___init__,
  f_cachetools___init___py__module__LFUCache___getitem__,
  f_cachetools___init___py__module__LFUCache___setitem__,
  f_cachetools___init___py__module__LFUCache___delitem__,
  f_cachetools___init___py__module__LFUCache_popitem,
  f_cachetools___init___py__module__LFUCache_clear,
  f_cachetools___init___py__module__LFUCache__LFUCache__touch,
  f_cachetools___init___py__module__LRUCache___init__,
  f_cachetools___init___py__module__LRUCache___getitem__,
  f_cachetools___init___py__module__LRUCache___setitem__,
  f_cachetools___init___py__module__LRUCache___delitem__,
  f_cachetools___init___py__module__LRUCache_popitem,
  f_cachetools___init___py__module__LRUCache_clear,
  f_cachetools___init___py__module__LRUCache__LRUCache__touch,
  f_cachetools___init___py__module__RRCache___init__,
  f_cachetools___init___py__module__RRCache_choice,
  f_cachetools___init___py__module__RRCache___setitem__,
  f_cachetools___init___py__module__RRCache___delitem__,
  f_cachetools___init___py__module__RRCache_popitem,
  f_cachetools___init___py__module__RRCache_clear,
  f_cachetools___init___py__module___TimedCache__Timer___init__,
  f_cachetools___init___py__module___TimedCache__Timer___call__,
  f_cachetools___init___py__module___TimedCache__Timer___enter__,
  f_cachetools___init___py__module___TimedCache__Timer___exit__,
  f_cachetools___init___py__module___TimedCache__Timer___reduce__,
  f_cachetools___init___py__module___TimedCache__Timer___getattr__,
  f_cachetools___init___py__module___TimedCache___init__,
  f_cachetools___init___py__module___TimedCache___repr__,
  f_cachetools___init___py__module___TimedCache___len__,
  f_cachetools___init___py__module___TimedCache_currsize,
  f_cachetools___init___py__module___TimedCache_timer,
  f_cachetools___init___py__module___TimedCache_get,
  f_cachetools___init___py__module___TimedCache_pop,
  f_cachetools___init___py__module___TimedCache_setdefault,
  f_cachetools___init___py__module___TimedCache_clear,
  f_cachetools___init___py__module___TimedCache_expire,
  f_cachetools___init___py__module__TTLCache__Link___init__,
  f_cachetools___init___py__module__TTLCache__Link___reduce__,
  f_cachetools___init___py__module__TTLCache__Link_unlink,
  f_cachetools___init___py__module__TTLCache___init__,
  f_cachetools___init___py__module__TTLCache___contains__,
  f_cachetools___init___py__module__TTLCache___getitem__,
  f_cachetools___init___py__module__TTLCache___setitem__,
  f_cachetools___init___py__module__TTLCache___delitem__,
  f_cachetools___init___py__module__TTLCache___iter__,
  f_cachetools___init___py__module__TTLCache___setstate__,
  f_cachetools___init___py__module__TTLCache___setstate____lambda_0,
  f_cachetools___init___py__module__TTLCache_ttl,
  f_cachetools___init___py__module__TTLCache_expire,
  f_cachetools___init___py__module__TTLCache_popitem,
  f_cachetools___init___py__module__TTLCache_clear,
  f_cachetools___init___py__module__TTLCache__TTLCache__getlink,
  f_cachetools___init___py__module__TLRUCache__Item___init__,
  f_cachetools___init___py__module__TLRUCache__Item___lt__,
  f_cachetools___init___py__module__TLRUCache___init__,
  f_cachetools___init___py__module__TLRUCache___contains__,
  f_cachetools___init___py__module__TLRUCache___getitem__,
  f_cachetools___init___py__module__TLRUCache___setitem__,
  f_cachetools___init___py__module__TLRUCache___delitem__,
  f_cachetools___init___py__module__TLRUCache___iter__,
  f_cachetools___init___py__module__TLRUCache_ttu,
  f_cachetools___init___py__module__TLRUCache_expire,
  f_cachetools___init___py__module__TLRUCache_popitem,
  f_cachetools___init___py__module__TLRUCache_clear,
  f_cachetools___init___py__module__TLRUCache__TLRUCache__getitem,
  f_cachetools___init___py__module__TLRUCache__TLRUCache__delitem,
  f_cachetools___init___py__module__cached,
  f_cachetools___init___py__module__cached_decorator,
  f_cachetools___init___py__module__cached_decorator_make_info_redefined_0,
  f_cachetools___init___py__module__cached_decorator_make_info_redefined_1,
  f_cachetools___init___py__module__cached_decorator_make_info,
  f_cachetools___init___py__module__cachedmethod,
  f_cachetools___init___py__module__cachedmethod_decorator,
  f_cachetools___init___py__module__cachedmethod_decorator_make_info,
  f_cachetools__cached_py__module___condition_info,
  f_cachetools__cached_py__module___condition_info_wrapper,
  f_cachetools__cached_py__module___condition_info_wrapper__lambda_0,
  f_cachetools__cached_py__module___condition_info_cache_clear,
  f_cachetools__cached_py__module___condition_info_cache_info,
  f_cachetools__cached_py__module___locked_info,
  f_cachetools__cached_py__module___locked_info_wrapper,
  f_cachetools__cached_py__module___locked_info_cache_clear,
  f_cachetools__cached_py__module___locked_info_cache_info,
  f_cachetools__cached_py__module___unlocked_info,
  f_cachetools__cached_py__module___unlocked_info_wrapper,
  f_cachetools__cached_py__module___unlocked_info_cache_clear,
  f_cachetools__cached_py__module___unlocked_info_cache_info,
  f_cachetools__cached_py__module___uncached_info,
  f_cachetools__cached_py__module___uncached_info_wrapper,
  f_cachetools__cached_py__module___uncached_info_cache_clear,
  f_cachetools__cached_py__module___uncached_info__lambda_1,
  f_cachetools__cached_py__module___condition,
  f_cachetools__cached_py__module___condition_wrapper,
  f_cachetools__cached_py__module___condition_wrapper__lambda_2,
  f_cachetools__cached_py__module___condition_cache_clear,
  f_cachetools__cached_py__module___locked,
  f_cachetools__cached_py__module___locked_wrapper,
  f_cachetools__cached_py__module___locked_cache_clear,
  f_cachetools__cached_py__module___unlocked,
  f_cachetools__cached_py__module___unlocked_wrapper,
  f_cachetools__cached_py__module___unlocked__lambda_3,
  f_cachetools__cached_py__module___uncached,
  f_cachetools__cached_py__module___uncached_wrapper,
  f_cachetools__cached_py__module___uncached__lambda_4,
  f_cachetools__cached_py__module___wrapper,
  f_cachetools__cachedmethod_py__module___warn_classmethod,
  f_cachetools__cachedmethod_py__module___warn_instance_dict,
  f_cachetools__cachedmethod_py__module___none,
  f_cachetools__cachedmethod_py__module___WrapperBase___init__,
  f_cachetools__cachedmethod_py__module___WrapperBase___call__,
  f_cachetools__cachedmethod_py__module___WrapperBase_cache_clear,
  f_cachetools__cachedmethod_py__module___WrapperBase_cache,
  f_cachetools__cachedmethod_py__module___WrapperBase_cache_key,
  f_cachetools__cachedmethod_py__module___WrapperBase_cache_lock,
  f_cachetools__cachedmethod_py__module___WrapperBase_cache_condition,
  f_cachetools__cachedmethod_py__module___DescriptorBase___init__,
  f_cachetools__cachedmethod_py__module___DescriptorBase___set_name__,
  f_cachetools__cachedmethod_py__module___DescriptorBase___get__,
  f_cachetools__cachedmethod_py__module___DeprecatedDescriptorBase___init__,
  f_cachetools__cachedmethod_py__module___DeprecatedDescriptorBase___call__,
  f_cachetools__cachedmethod_py__module___DeprecatedDescriptorBase_cache_clear,
  f_cachetools__cachedmethod_py__module___condition_info,
  f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper___init__,
  f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper___call__,
  f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper___call____lambda_0,
  f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper_cache_clear,
  f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper_cache_info,
  f_cachetools__cachedmethod_py__module___locked_info,
  f_cachetools__cachedmethod_py__module___locked_info_Descriptor_Wrapper___init__,
  f_cachetools__cachedmethod_py__module___locked_info_Descriptor_Wrapper___call__,
  f_cachetools__cachedmethod_py__module___locked_info_Descriptor_Wrapper_cache_clear,
  f_cachetools__cachedmethod_py__module___locked_info_Descriptor_Wrapper_cache_info,
  f_cachetools__cachedmethod_py__module___unlocked_info,
  f_cachetools__cachedmethod_py__module___unlocked_info_Descriptor_Wrapper___init__,
  f_cachetools__cachedmethod_py__module___unlocked_info_Descriptor_Wrapper___call__,
  f_cachetools__cachedmethod_py__module___unlocked_info_Descriptor_Wrapper_cache_clear,
  f_cachetools__cachedmethod_py__module___unlocked_info_Descriptor_Wrapper_cache_info,
  f_cachetools__cachedmethod_py__module___condition,
  f_cachetools__cachedmethod_py__module___condition_wrapper,
  f_cachetools__cachedmethod_py__module___condition_wrapper__lambda_1,
  f_cachetools__cachedmethod_py__module___condition_cache_clear,
  f_cachetools__cachedmethod_py__module___condition_classmethod_wrapper,
  f_cachetools__cachedmethod_py__module___condition_Descriptor_Wrapper___init__,
  f_cachetools__cachedmethod_py__module___condition_Descriptor_Wrapper___call__,
  f_cachetools__cachedmethod_py__module___condition_Descriptor_Wrapper_cache_clear,
  f_cachetools__cachedmethod_py__module___locked,
  f_cachetools__cachedmethod_py__module___locked_wrapper,
  f_cachetools__cachedmethod_py__module___locked_cache_clear,
  f_cachetools__cachedmethod_py__module___locked_Descriptor_Wrapper___init__,
  f_cachetools__cachedmethod_py__module___locked_Descriptor_Wrapper___call__,
  f_cachetools__cachedmethod_py__module___locked_Descriptor_Wrapper_cache_clear,
  f_cachetools__cachedmethod_py__module___unlocked,
  f_cachetools__cachedmethod_py__module___unlocked_wrapper,
  f_cachetools__cachedmethod_py__module___unlocked_cache_clear,
  f_cachetools__cachedmethod_py__module___unlocked_Descriptor_Wrapper___init__,
  f_cachetools__cachedmethod_py__module___unlocked_Descriptor_Wrapper___call__,
  f_cachetools__cachedmethod_py__module___unlocked_Descriptor_Wrapper_cache_clear,
  f_cachetools__cachedmethod_py__module___wrapper,
  f_cachetools_func_py__module___UnboundTTLCache___init__,
  f_cachetools_func_py__module___UnboundTTLCache_maxsize,
  f_cachetools_func_py__module___cache,
  f_cachetools_func_py__module___cache_decorator,
  f_cachetools_func_py__module___cache_decorator__lambda_0,
  f_cachetools_func_py__module__fifo_cache,
  f_cachetools_func_py__module__lfu_cache,
  f_cachetools_func_py__module__lru_cache,
  f_cachetools_func_py__module__rr_cache,
  f_cachetools_func_py__module__ttl_cache,
  f_cachetools_keys_py__module___HashedTuple___hash__,
  f_cachetools_keys_py__module___HashedTuple___add__,
  f_cachetools_keys_py__module___HashedTuple___radd__,
  f_cachetools_keys_py__module___HashedTuple___getstate__,
  f_cachetools_keys_py__module__hashkey,
  f_cachetools_keys_py__module__methodkey,
  f_cachetools_keys_py__module__typedkey,
  f_cachetools_keys_py__module__typedmethodkey,
  f__module_objects___module_,
  f_cachetools__cached_py__module_,
  f_cachetools__cachedmethod_py__module_,
  f_cachetools___init___py__module_,
  f_cachetools_func_py__module_,
  f_cachetools_keys_py__module_
] }

end Autoform.Generated.Cachetools