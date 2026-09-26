"""Heap preservation includes payloads, captures, versions and exact value state."""
from test_source_numeric import ROOT, numeric_env, run


def test_heap_preservation_kernel(tmp_path, numeric_env):
    run(['lake', 'build', 'Autoform.SpecsGen.Basis'], ROOT, numeric_env, timeout=600)
    path = tmp_path / 'HeapPreservation.lean'
    path.write_text(r'''import Autoform.SpecsGen.Basis
open Autoform.Core Autoform.SpecsGen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def object : Obj := { cls := "C", fields := [("value", .int 1)] }
example : Obj.beq object object = true := by decide +kernel
example : Obj.beq object { object with cls := "D" } = false := by decide +kernel
example : Obj.beq object { object with fields := [("value", .float (Fl.ofBits 4607182418800017408))] }
    = false := by decide +kernel
example : Obj.beq object { object with captured := [("outer", .int 1)] }
    = false := by decide +kernel
example : Obj.beq object { object with version := 1 } = false := by decide +kernel
example : Obj.beq object { object with payload := .list [] } = false := by decide +kernel
example : Obj.beq { object with payload := .list [.int 1] }
    { object with payload := .list [.int 2] } = false := by decide +kernel
example : Obj.beq { object with payload := .dict [(.int 1, .int 2)] }
    { object with payload := .dict [(.int 1, .int 3)] } = false := by decide +kernel
example : Obj.beq { object with payload := .tuple [.int 1] }
    { object with payload := .list [.int 1] } = false := by decide +kernel
example : Val.stateEq (.clos "f" [("x", .int 1)]) (.clos "f" [("x", .int 2)])
    = false := by decide +kernel
example : Val.stateEq (.clsClos "C" [("x", .int 1)]) (.clsClos "C" [("x", .int 2)])
    = false := by decide +kernel
example : Val.stateEq (.bobj "A" (.tuple [.int 1])) (.bobj "B" (.tuple [.int 1]))
    = false := by decide +kernel
example : Val.stateEq (.float (Fl.ofBits 0)) (.float (Fl.ofBits 9223372036854775808))
    = false := by decide +kernel
example : Val.stateEq (.float (Fl.ofBits 9221120237041090560))
    (.float (Fl.ofBits 9221120237041090560)) = true := by decide +kernel

def ctx : Ctx := { table := [], dialect := .python }
def initial : Case :=
  { heap := [{ cls := "list", fields := [], payload := .list [.int 1] }],
    self := none, args := [.ref 0] }
def append : Func :=
  { name := "append", params := ["xs"],
    body := .expr (.mcall (.name "xs") "append" [.lit (.int 2)]) }
def readLength : Func :=
  { name := "readLength", params := ["xs"],
    body := .ret (.call "len" [.name "xs"]) }
def restoreContents : Func :=
  { name := "restoreContents", params := ["xs"],
    body := .seq append.body (.expr (.mcall (.name "xs") "pop" [])) }
example : (runCase ctx 30 append initial).2 = .val .unit := by rfl
example : lawHeapPreserved ctx 30 append initial = false := by decide +kernel
example : lawHeapPreserved ctx 30 readLength initial = true := by decide +kernel
example : lawHeapPreserved ctx 30 restoreContents initial = false := by decide +kernel
''')
    run(['lake', 'env', 'lean', path], ROOT, numeric_env, timeout=180)
