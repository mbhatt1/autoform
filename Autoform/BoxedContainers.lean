import Autoform.Lang.Core.Semantics

/-!
# Boxed Python containers, pinned by evaluation

`docs/boxed-containers.md` steps 3-4. Each theorem runs a small Core program -- written in
exactly the shape `cartographer/export_ast.sc` emits for the Python source quoted above it
(a display is `Expr.boxContainer` around a `listE`/`dictE`) -- and states CPython's answer.
They are checked by kernel evaluation (`rfl`/`decide`), so each one dies under the mutation
it guards: a `setIndex` that wrote back through the receiver expression, a `Heap.view` that
forgot a payload, an `index` that clamped a negative index, an `in` or `==` that compared
boxed references by address.

The same programs are run against CPython by `tests/test_boxed_containers.py`, through the
real exporter's output rather than these hand-written terms.
-/

namespace Autoform.Core.BoxedContainers

open Autoform.Core

/-- A Python list display. -/
private abbrev L (es : List Expr) : Expr := .boxContainer (.listE es)
/-- The Python empty-dict display. -/
private abbrev D : Expr := .boxContainer (.dictE [])
private abbrev n (i : Int) : Expr := .lit (.int i)
private abbrev s (t : String) : Expr := .lit (.str t)
private abbrev v (x : String) : Expr := .name x

/-- Run a zero-argument Python function body. -/
private def run (body : Stmt) : EResult :=
  runFunc { funcs := [{ name := "f", params := [], body := body }] } 200 "f" []

/-- Statement sequencing, right-nested as the exporter emits it. -/
private def seqs : List Stmt → Stmt
  | []      => .skip
  | [x]     => x
  | x :: xs => .seq x (seqs xs)

/-- The project's own question: `b = [0, 5]; a = b; b[0] = 1; return a[0]` is `1`. -/
theorem alias_write_visible :
    run (seqs [.assign "b" (L [n 0, n 5]), .assign "a" (v "b"),
               .setIndex (v "b") (n 0) (n 1), .ret (.index (v "a") (n 0))])
      = .val (.int 1) := by rfl

/-- The same program over an UNBOXED list -- what every corpus rendered before this change
still contains -- is the original hole, not a wrong `0`: value semantics cannot honour
the write, so it refuses. -/
theorem unboxed_write_still_holes :
    run (seqs [.assign "b" (.listE [n 0, n 5]), .assign "a" (v "b"),
               .setIndex (v "b") (n 0) (n 1), .ret (.index (v "a") (n 0))])
      = .hole "setIndex:immutable-containers" := by rfl

/-- Two displays are two objects: `a = []; b = []; b.append(1); return len(a)` is `0`. -/
theorem displays_do_not_alias :
    run (seqs [.assign "a" (L []), .assign "b" (L []),
               .expr (.mcall (v "b") "append" [n 1]), .ret (.call "len" [v "a"])])
      = .val (.int 0) := by rfl

/-- `a = []; b = a; b.append(1); b.append(2); x = a.pop(); return len(a) * 10 + x` is `12`:
the mutating methods write through the reference, not through the receiver expression. -/
theorem append_pop_through_alias :
    run (seqs [.assign "a" (L []), .assign "b" (v "a"),
               .expr (.mcall (v "b") "append" [n 1]), .expr (.mcall (v "b") "append" [n 2]),
               .assign "x" (.mcall (v "a") "pop" []),
               .ret (.binop "+" (.binop "*" (.call "len" [v "a"]) (n 10)) (v "x"))])
      = .val (.int 12) := by rfl

/-- The CPG's own desugaring of `self.d.pop(k)` is `t = self.d; t.pop(k)`; the pop must
reach `self.d`. Here `t = d; t.pop('k'); return len(d)` is `0`. -/
theorem pop_through_temporary :
    run (seqs [.assign "d" D, .setIndex (v "d") (s "k") (n 1),
               .assign "t" (v "d"), .expr (.mcall (v "t") "pop" [s "k"]),
               .ret (.call "len" [v "d"])])
      = .val (.int 0) := by rfl

/-- `d = {}; d['k'] = 1; e = d; e['j'] = 2; return d['j'] * 10 + d['k']` is `21`. -/
theorem dict_set_get_through_alias :
    run (seqs [.assign "d" D, .setIndex (v "d") (s "k") (n 1), .assign "e" (v "d"),
               .setIndex (v "e") (s "j") (n 2),
               .ret (.binop "+" (.binop "*" (.index (v "d") (s "j")) (n 10))
                                (.index (v "d") (s "k")))])
      = .val (.int 21) := by rfl

/-- Insertion order: `d['b'] = 1; d['a'] = 2; d['b'] = 3` keeps `b` FIRST, with value 3.
`list(d) == ['b', 'a']` is `True`, and the dict equals `{'a': 2, 'b': 3}` in either order. -/
theorem dict_insertion_order :
    run (seqs [.assign "d" D, .setIndex (v "d") (s "b") (n 1), .setIndex (v "d") (s "a") (n 2),
               .setIndex (v "d") (s "b") (n 3),
               .ret (.binop "==" (.call "list" [v "d"]) (L [s "b", s "a"]))])
      = .val (.bool true) := by rfl

theorem dict_eq_is_order_insensitive :
    run (seqs [.assign "d" D, .setIndex (v "d") (s "b") (n 3), .setIndex (v "d") (s "a") (n 2),
               .assign "e" D, .setIndex (v "e") (s "a") (n 2), .setIndex (v "e") (s "b") (n 3),
               .ret (.binop "==" (v "d") (v "e"))])
      = .val (.bool true) := by rfl

/-- `xs = [1, 2, 3]; xs[-1] = 9; return xs[-1] + xs[0]` is `10`. Before this change the
read `xs[-1]` was clamped to `xs[0]`. -/
theorem negative_index :
    run (seqs [.assign "xs" (L [n 1, n 2, n 3]), .setIndex (v "xs") (n (-1)) (n 9),
               .ret (.binop "+" (.index (v "xs") (n (-1))) (.index (v "xs") (n 0)))])
      = .val (.int 10) := by rfl

/-- `[7, 8, 9][-1]` on an unboxed tuple too: `9`, not `7`. -/
theorem negative_index_read_tuple :
    run (.ret (.index (.tupleE [n 7, n 8, n 9]) (n (-1)))) = .val (.int 9) := by rfl

/-- Out of range, both directions: `IndexError`. -/
theorem write_out_of_range :
    run (seqs [.assign "xs" (L [n 1]), .setIndex (v "xs") (n 3) (n 2), .ret (n 0)])
      = .exn (.str "IndexError") := by rfl
theorem write_out_of_range_neg :
    run (seqs [.assign "xs" (L [n 1]), .setIndex (v "xs") (n (-2)) (n 2), .ret (n 0)])
      = .exn (.str "IndexError") := by rfl
theorem read_out_of_range :
    run (seqs [.assign "xs" (L [n 1]), .ret (.index (v "xs") (n 1))])
      = .exn (.str "IndexError") := by rfl

/-- A missing key is `KeyError`, for a read and for `del`. -/
theorem missing_key :
    run (seqs [.assign "d" D, .ret (.index (v "d") (s "missing"))])
      = .exn (.str "KeyError") := by rfl
theorem del_missing_key :
    run (seqs [.assign "d" D, .delIndex (v "d") (s "missing"), .ret (n 0)])
      = .exn (.str "KeyError") := by rfl

/-- `del d['a']` removes it: `d = {}; d['a'] = 1; del d['a']; return len(d)` is `0`;
`del xs[0]` on `[1, 2]` leaves `[2]`. -/
theorem del_key :
    run (seqs [.assign "d" D, .setIndex (v "d") (s "a") (n 1), .delIndex (v "d") (s "a"),
               .ret (.call "len" [v "d"])])
      = .val (.int 0) := by rfl
theorem del_position :
    run (seqs [.assign "xs" (L [n 1, n 2]), .delIndex (v "xs") (n 0),
               .ret (.index (v "xs") (n 0))])
      = .val (.int 2) := by rfl

/-- Item assignment on a tuple or a string is CPython's `TypeError`, a modelled answer. -/
theorem tuple_item_assignment :
    run (seqs [.assign "t" (.tupleE [n 1, n 2]), .setIndex (v "t") (n 0) (n 3), .ret (n 0)])
      = .exn (.str "TypeError") := by rfl

/-- A list is unhashable: `d[[1]] = 2` is `TypeError`. -/
theorem unhashable_key :
    run (seqs [.assign "d" D, .setIndex (v "d") (L [n 1]) (n 2), .ret (n 0)])
      = .exn (.str "TypeError") := by rfl

/-- `==` compares contents, `is` compares objects: `[1] == [1]` but not `[1] is [1]`;
`x is x`. -/
theorem eq_is_value :
    run (.ret (.binop "==" (L [n 1]) (L [n 1]))) = .val (.bool true) := by rfl
theorem is_is_identity :
    run (.ret (.isOp false (L [n 1]) (L [n 1]))) = .val (.bool false) := by rfl
theorem is_self :
    run (seqs [.assign "x" (L [n 1]), .ret (.isOp false (v "x") (v "x"))])
      = .val (.bool true) := by rfl

/-- Membership compares elements by value through the heap: `[1] in [[1]]`. -/
theorem in_by_value :
    run (.ret (.inOp false (L [n 1]) (L [L [n 1]]))) = .val (.bool true) := by rfl

/-- Truthiness reads the payload: `if []: return 1` falls through; `not []` is `True`. -/
theorem empty_list_falsy :
    run (seqs [.assign "a" (L []), .ifte (v "a") (.ret (n 1)) .skip, .ret (n 2)])
      = .val (.int 2) := by rfl
theorem not_empty_list :
    run (.ret (.unop "!" (L []))) = .val (.bool true) := by rfl

/-- `list(a)` is a fresh object: `a = [1]; b = list(a); b.append(2); return len(a)` is `1`. -/
theorem list_copy_is_fresh :
    run (seqs [.assign "a" (L [n 1]), .assign "b" (.call "list" [v "a"]),
               .expr (.mcall (v "b") "append" [n 2]), .ret (.call "len" [v "a"])])
      = .val (.int 1) := by rfl

/-- Iteration over a boxed list reads its contents ... -/
theorem for_over_boxed :
    run (seqs [.assign "t" (n 0),
               .forIn "x" (L [n 1, n 2, n 3]) (.assign "t" (.binop "+" (v "t") (v "x"))),
               .ret (v "t")])
      = .val (.int 6) := by rfl

/-- ... and REFUSES when the loop writes to the object it iterates: CPython's list iterator
would have seen the write, and Core iterated a snapshot. A hole, not a guess. -/
theorem mutate_during_iteration :
    run (seqs [.assign "xs" (L [n 1]),
               .forIn "x" (v "xs") (.expr (.mcall (v "xs") "append" [n 2])),
               .ret (n 0)])
      = .hole "forIn:container-mutated-during-iteration" := by rfl

/-- A dict view would go stale after the next write, so it is not modelled. -/
theorem dict_view_not_modelled :
    run (seqs [.assign "d" D, .ret (.mcall (v "d") "keys" [])])
      = .hole "mcall:dict.keys:live-view-not-modelled" := by rfl

/-- A list has no attributes; reading one is not `None`. -/
theorem list_attribute_holes :
    run (seqs [.assign "xs" (L []), .ret (.field (v "xs") "foo")])
      = .hole "field:foo:builtin-container" := by rfl

end Autoform.Core.BoxedContainers
