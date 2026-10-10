import Autoform.Refine
import Autoform.Generated.Cachetools
import Autoform.Specs.CachetoolsSpec.Base

/-! Part 7 of 7 of `Autoform/Specs/CachetoolsSpec.lean`: the `_Link.unlink` specification
against the ring representation (`Refine.DRing`), added on `hyperscale-shards` (roadmap 2.1).
The context is `CachetoolsSpec/Base.lean`. -/

namespace Autoform.Specs.Cachetools

open Autoform.Core Autoform.Refine Autoform.Generated.Cachetools

-- `local` attributes do not cross files; the same simp set as the single-file module.
attribute [local simp] Ctx.classLookupGap Ctx.usesClassMetadata Ctx.isProperty
  Ctx.classStorageKey Ctx.fieldWriteCheck Ctx.fieldWriteKey Ctx.readSlot Ctx.isSharedClassValue

/-! ### `TTLCache._Link.unlink` — the eviction primitive, against a heap representation

`TTLCache` keeps its entries on a doubly-linked ring through a sentinel (`self.__root`),
ordered by expiry; `expire` and `popitem` evict by walking the ring and calling
`link.unlink()` on each victim:

    def unlink(self):
        next = self.next
        prev = self.prev
        prev.next = next
        next.prev = prev

This is the function `Refine.lean` obligation (4) was about: its effect is on two *other*
objects, reached through pointers read from the receiver, and no statement about a single
object can specify it. The specification here is in two layers.

`TTLLink_unlink_mrefines` is the exact equation (`MRefines`, result and post-heap) for any
heap in which `self` is a `_Link` whose two slots hold references to `_Link`s: the heap
afterwards is `self.prev` with its `next` slot written and `self.next` with its `prev` slot
written, nothing else, and the result is `None`.

`TTLLink_unlink_ring` is the **functional specification against the representation
predicate**: for every heap holding a ring `root :: L₁ ++ x :: L₂` of `_Link` nodes on
pairwise-distinct addresses (`Refine.DRing`), and every fuel budget of at least 8,
`unlink` on `x` terminates with `None` and the heap holds the ring `L₁ ++ L₂`; every
address other than `x`'s two neighbours — `x` itself included — is untouched. The
quantification is over the heap and the ring's length; nothing in it is a finite-domain
witness. The whole proof is the generic `DRing.unlink` (heap algebra on `Represents`,
no interpreter) applied to one evaluation of the body (`execStmt_dlink_unlink`); what is
specific to `cachetools` below is only the class-metadata facts — `next` and `prev` are
slots of `TTLCache._Link` with their own storage keys, and `_Link` has `object`'s
`__setattr__` — and the `rfl` that the generated body is the body `Refine.lean` reasons
about (`TTLLink_unlink_body`). That `rfl` is what makes the mutation gate bite: a mutant of
the generated `unlink` fails there.

What this does **not** say: that the ring is the one `TTLCache` built. `DRing` is a
predicate on a heap region, and the theorem holds for any heap satisfying it, which is the
point; connecting it to a `TTLCache` instance's `__root` through `__init__`, `__setitem__`
and the `OrderedDict` payload is the container-representation work §5 still lists. -/

/-- The class, and the storage keys its two pointer slots are kept under (`__slots__`). -/
abbrev LinkCls : String := "cachetools/__init__.py:<module>.TTLCache._Link"
abbrev linkPrevKey : String := "<slot>cachetools/__init__.py:<module>.TTLCache._Link.prev"
abbrev linkNextKey : String := "<slot>cachetools/__init__.py:<module>.TTLCache._Link.next"

theorem lookup_Link_next (ctx : Ctx) (hc : ctx.classDecls = P.classDecls) :
    ctx.classLookup LinkCls "next" = .found LinkCls (.slot linkNextKey) := by
  unfold Ctx.classLookup; rw [hc]; decide +kernel
theorem lookup_Link_prev (ctx : Ctx) (hc : ctx.classDecls = P.classDecls) :
    ctx.classLookup LinkCls "prev" = .found LinkCls (.slot linkPrevKey) := by
  unfold Ctx.classLookup; rw [hc]; decide +kernel

theorem ctxP_dialect : (ctxOf P).dialect = Dialect.python := rfl
theorem ctxP_classDecls : (ctxOf P).classDecls.isEmpty = false := rfl

/-- `_Link` is a declared class, so attribute access on it goes through the recovered
hierarchy rather than the instance dictionary. -/
theorem link_meta : (ctxOf P).usesClassMetadata LinkCls = true := by
  decide +kernel

theorem link_gap_next : (ctxOf P).classLookupGap LinkCls "next" = none := by
  simp [-Ctx.usesClassMetadata, Ctx.classLookupGap, lookup_Link_next (ctxOf P) rfl]
theorem link_gap_prev : (ctxOf P).classLookupGap LinkCls "prev" = none := by
  simp [-Ctx.usesClassMetadata, Ctx.classLookupGap, lookup_Link_prev (ctxOf P) rfl]

/-- A slot read is a read of the storage key. -/
theorem link_readSlot_next {o : Obj} {v : Val} (hc : o.cls = LinkCls)
    (hf : o.fields.find? (·.1 == linkNextKey) = some (linkNextKey, v)) :
    (ctxOf P).readSlot o "next" = some (.val v) := by
  simp [-Ctx.usesClassMetadata, Ctx.readSlot, hc, link_meta, lookup_Link_next (ctxOf P) rfl, hf]
theorem link_readSlot_prev {o : Obj} {v : Val} (hc : o.cls = LinkCls)
    (hf : o.fields.find? (·.1 == linkPrevKey) = some (linkPrevKey, v)) :
    (ctxOf P).readSlot o "prev" = some (.val v) := by
  simp [-Ctx.usesClassMetadata, Ctx.readSlot, hc, link_meta, lookup_Link_prev (ctxOf P) rfl, hf]

/-- A slot write passes `object.__setattr__`'s check and lands under the storage key. -/
theorem link_writeCheck_next {h : Heap} {r : Ref} {o : Obj} (ho : h.get r = some o)
    (hc : o.cls = LinkCls) : (ctxOf P).fieldWriteCheck h r "next" = .val .unit := by
  simp [-Ctx.usesClassMetadata, Ctx.fieldWriteCheck, ctxP_dialect, ctxP_classDecls, ho, hc,
    link_meta, lookup_Link_setattr (ctxOf P) rfl, lookup_Link_next (ctxOf P) rfl]
theorem link_writeCheck_prev {h : Heap} {r : Ref} {o : Obj} (ho : h.get r = some o)
    (hc : o.cls = LinkCls) : (ctxOf P).fieldWriteCheck h r "prev" = .val .unit := by
  simp [-Ctx.usesClassMetadata, Ctx.fieldWriteCheck, ctxP_dialect, ctxP_classDecls, ho, hc,
    link_meta, lookup_Link_setattr (ctxOf P) rfl, lookup_Link_prev (ctxOf P) rfl]
theorem link_writeKey_next {h : Heap} {r : Ref} {o : Obj} (ho : h.get r = some o)
    (hc : o.cls = LinkCls) : (ctxOf P).fieldWriteKey h r "next" = linkNextKey := by
  simp [-Ctx.usesClassMetadata, Ctx.fieldWriteKey, ctxP_dialect, ctxP_classDecls, ho, hc,
    link_meta, lookup_Link_next (ctxOf P) rfl]
theorem link_writeKey_prev {h : Heap} {r : Ref} {o : Obj} (ho : h.get r = some o)
    (hc : o.cls = LinkCls) : (ctxOf P).fieldWriteKey h r "prev" = linkPrevKey := by
  simp [-Ctx.usesClassMetadata, Ctx.fieldWriteKey, ctxP_dialect, ctxP_classDecls, ho, hc,
    link_meta, lookup_Link_prev (ctxOf P) rfl]

/-- The representation of one `TTLCache._Link` node: `Refine.dlinkRep` at this class and
its two slot storage keys. `Represents ttlLinkRep h r ⟨p, n⟩` reads "the `_Link` at `r`
has `prev = p` and `next = n`". -/
def ttlLinkRep : HeapRep DLink := dlinkRep LinkCls linkPrevKey linkNextKey

/-- A field write changes no object's class. -/
theorem HasClass.setField {h : Heap} {r s : Ref} {f : String} {v : Val} {cls : String}
    (hc : HasClass h r cls) : HasClass (h.setField s f v) r cls := by
  obtain ⟨o, ho, hcls⟩ := hc
  have := @Heap.cls_setField h s r f v
  rw [ho] at this
  cases hg : (h.setField s f v).get r with
  | none => rw [hg] at this; simp at this
  | some o' =>
    rw [hg] at this
    simp only [Option.map_some, Option.some.injEq] at this
    exact ⟨o', hg, this.trans hcls⟩

/-- The generated body is the body `Refine.lean` reasons about. This is the one line a
mutant of `unlink` in `Generated/Cachetools.lean` has to get past, and cannot. -/
theorem TTLLink_unlink_body :
    f_cachetools___init___py__module__TTLCache__Link_unlink.body = dlinkUnlinkBody := rfl

/-- One call of the generated `unlink`, for any heap in which `self` is a `_Link` with
`prev = p` and `next = n` and both neighbours are `_Link`s. -/
theorem TTLLink_unlink_step (k : Nat) (h : Heap) {x p n : Ref}
    (hx : Represents ttlLinkRep h x ⟨p, n⟩)
    (hp : HasClass h p LinkCls) (hn : HasClass h n LinkCls) :
    applyFunc (ctxOf P) (k+8) h f_cachetools___init___py__module__TTLCache__Link_unlink
        (some (.ref x)) [] []
      = ((h.setField p linkNextKey (.ref n)).setField n linkPrevKey (.ref p), .val .unit) := by
  obtain ⟨ox, hox, hcx, hfp, hfn⟩ := dlink_fields hx
  obtain ⟨op, hop, hcp⟩ := hp
  obtain ⟨on', hon', hcn'⟩ := hn.setField (s := p) (f := linkNextKey) (v := .ref n)
  have hjs : (ctxOf P).dialect ≠ .javascript := by
    rw [ctxP_dialect]; decide
  have hbody : execStmt (ctxOf P) (k+7) h [("self", .ref x)]
        f_cachetools___init___py__module__TTLCache__Link_unlink.body
      = ((h.setField p linkNextKey (.ref n)).setField n linkPrevKey (.ref p),
         .normal (Env.set (Env.set [("self", .ref x)] "next" (.ref n)) "prev" (.ref p))) := by
    rw [TTLLink_unlink_body]
    exact execStmt_dlink_unlink (ctxOf P) k h [("self", .ref x)] hjs rfl rfl rfl hox
      (hcx ▸ link_gap_next) (hcx ▸ link_gap_prev)
      (link_readSlot_next hcx hfn) (link_readSlot_prev hcx hfp)
      (link_writeCheck_next hop hcp) (link_writeKey_next hop hcp)
      (link_writeCheck_prev hon' hcn') (link_writeKey_prev hon' hcn')
  exact applyFunc_method_normal (ctxOf P) (k+7) h _ _ rfl rfl rfl rfl hbody

/-- The node at `x` as the heap presents it, if it is a `_Link` with both pointers. -/
def linkOf (h : Heap) (x : Ref) : Option DLink := (h.get x).bind ttlLinkRep.abs

/-- **`unlink`, exactly.** Result `None`; heap: `self.prev`'s `next` slot and `self.next`'s
`prev` slot rewritten, in that order, nothing else. Stated with `Heap.setField` on the
right so that the rest of the heap is neither assumed nor lost, as `Timer_exit_mrefines`
does. The domain asks for the three objects to be `_Link`s: the receiver because its
slots are read, the neighbours because a slot write consults the receiver's class. -/
theorem TTLLink_unlink_mrefines :
    MRefines "cachetools/__init__.py:<module>.TTLCache._Link.unlink" 8
      (fun h self args => ∃ x a, self = .ref x ∧ args = [] ∧ Represents ttlLinkRep h x a
                            ∧ HasClass h a.prev LinkCls ∧ HasClass h a.next LinkCls)
      (fun h self _ => match self with
        | .ref x => match linkOf h x with
          | some a => ((h.setField a.prev linkNextKey (.ref a.next)).setField a.next linkPrevKey (.ref a.prev),
                       .ret .unit)
          | none   => (h, .ret .unit)
        | _ => (h, .ret .unit)) := by
  rintro h _ _ ⟨x, ⟨p, n⟩, rfl, rfl, hx, hp, hn⟩
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__TTLCache__Link_unlink rfl]
  have hlink : linkOf h x = some ⟨p, n⟩ := by
    obtain ⟨o, ho, _, ha⟩ := hx
    simp [linkOf, ho, ha]
  simp only [hlink, Outcome.toEResult_ret]
  exact TTLLink_unlink_step k h hx hp hn

/-- **`unlink` removes its node from the ring — for every ring.** The functional
specification against the representation predicate: in any heap holding the ring
`root :: L₁ ++ x :: L₂` of `_Link`s on distinct addresses, `x.unlink()` leaves the ring
`root :: L₁ ++ L₂`, returns `None`, and changes no address but `x`'s two neighbours. -/
theorem TTLLink_unlink_ring (h : Heap) (root x : Ref) (L₁ L₂ : List Ref)
    (hring : DRing ttlLinkRep h root (L₁ ++ x :: L₂))
    (hnd : (root :: (L₁ ++ x :: L₂)).Nodup) (fuel : Nat) (hf : 8 ≤ fuel) :
    ∃ h', runMethod fuel h "cachetools/__init__.py:<module>.TTLCache._Link.unlink" (.ref x) []
            = (h', .val .unit)
      ∧ DRing ttlLinkRep h' root (L₁ ++ L₂)
      ∧ (∀ s, s ≠ L₁.getLastD root → s ≠ L₂.headD root → h'.get s = h.get s)
      ∧ h'.get x = h.get x := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 8 := ⟨fuel - 8, by omega⟩
  have hu := DRing.unlink (cls := LinkCls) (kp := linkPrevKey) (kn := linkNextKey)
    (by decide) rfl rfl hring hnd
  obtain ⟨hx, hring'⟩ := hu
  have hcls : ∀ y, y ∈ root :: (L₁ ++ x :: L₂) → HasClass h y LinkCls := by
    intro y hy
    obtain ⟨a, o, ho, hc, _⟩ := DRing.mem hring hy
    exact ⟨o, ho, hc⟩
  have hp : HasClass h (L₁.getLastD root) LinkCls := by
    apply hcls
    rcases List.mem_cons.mp (getLastD_mem_cons L₁ root) with e | m
    · rw [e]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ m)
  have hn : HasClass h (L₂.headD root) LinkCls := by
    apply hcls
    rcases List.mem_cons.mp (headD_mem_cons L₂ root) with e | m
    · rw [e]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ m))
  -- `x` is neither of its own neighbours: the ring has no repeated address
  rw [List.nodup_cons, List.nodup_append, List.nodup_cons] at hnd
  obtain ⟨hroot_nin, hnd₁, ⟨hx_nin₂, _⟩, hdisj⟩ := hnd
  have hxp : x ≠ L₁.getLastD root := by
    rcases List.mem_cons.mp (getLastD_mem_cons L₁ root) with e | m
    · rw [e]; exact fun e' => hroot_nin (e' ▸ List.mem_append_right _ List.mem_cons_self)
    · exact fun e' => hdisj _ m x List.mem_cons_self e'.symm
  have hxn : x ≠ L₂.headD root := by
    rcases List.mem_cons.mp (headD_mem_cons L₂ root) with e | m
    · rw [e]; exact fun e' => hroot_nin (e' ▸ List.mem_append_right _ List.mem_cons_self)
    · exact fun e' => hx_nin₂ (e' ▸ m)
  refine ⟨_, ?_, hring', ?_, ?_⟩
  · rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__TTLCache__Link_unlink rfl]
    exact TTLLink_unlink_step k h hx hp hn
  · intro s hsp hsn
    rw [Heap.get_setField_of_ne hsn, Heap.get_setField_of_ne hsp]
  · rw [Heap.get_setField_of_ne hxn, Heap.get_setField_of_ne hxp]

-- No admitted step, no `native_decide`; and the ring theorem mentions the generated
-- function and the representation predicate, so it is not dependency-vacuous.
#audit_axioms TTLLink_unlink_mrefines
#audit_axioms TTLLink_unlink_ring
#audit_depends TTLLink_unlink_ring on f_cachetools___init___py__module__TTLCache__Link_unlink DRing dlinkRep

end Autoform.Specs.Cachetools
