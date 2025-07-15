import Mathlib.Order.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort
import LeanScratch.Domain.Dom
import LeanScratch.Domain.Lub
import LeanScratch.Domain.Continous
import LeanScratch.Fin2
import LeanScratch.HEq

namespace Dom

namespace C

variable [ida : PartialOrder α] {c : C α}

structure Finite' (c : C α) : Type _ where
   ls : List α
   ordered : List.Sorted ida.lt ls
   allMem n : c n ∈ ls
   memAll x (h : x ∈ ls) : ∃ n, c n = x

def Finite'.nodup (f : Finite' c) : f.ls.Nodup :=
  f.ordered.rec .nil
    (λ all_lt _ ih ↦ .cons (λ h ↦ (lt_self_iff_false _).mp $ all_lt _ h) ih)

-- TODO: Migrate this all to a function like extractor, make it computable
structure Finite (c : C α) : Type _ where
  ls : List α
  ordered : List.Pairwise ida.lt ls

  extractor (n : Nat) : Fin ls.length
  extractor_agrees (n : Nat) : c n = ls.get (extractor n)
  sur : Function.Surjective extractor

namespace Finite

section equiv

noncomputable def extractor.of
    {ls : List α}
    (allMem : ∀ n, c n ∈ ls)
    (n : Nat)
    : Fin ls.length :=
  Classical.choose $ List.mem_iff_get.mp $ allMem n

theorem extractor_agrees.of
    {ls : List α}
    {allMem : ∀ n, c n ∈ ls}
    (n : Nat)
    : c n = ls.get (extractor.of allMem n) :=
  (Classical.choose_spec $ List.mem_iff_get.mp $ allMem n).symm

def nodup (f : Finite c) : f.ls.Nodup :=
  f.ordered.rec .nil
    (λ all_lt _ ih ↦ .cons (λ h ↦ (lt_self_iff_false _).mp $ all_lt _ h) ih)

theorem sur.of
    {ls : List α}
    {allMem : ∀ n, c n ∈ ls}
    (nodup : ls.Nodup)
    (memAll : (x : α) → x ∈ ls → ∃ n, c n = x)
    : Function.Surjective (extractor.of allMem) := fun res =>
  have ⟨w, p⟩ := memAll _ $ List.get_mem _ res.val res.prop
  ⟨w, List.nodup_iff_injective_get.mp nodup $ (extractor_agrees.of _).symm.trans p⟩

noncomputable def ofFinite' (f : Finite' c) : Finite c where
  ls := f.ls
  ordered := f.ordered
  extractor := extractor.of f.allMem
  extractor_agrees := extractor_agrees.of
  sur := sur.of f.nodup f.memAll

def memAll (fin : Finite c) (x : α) (hmem : x ∈ fin.ls) : ∃ n, c n = x := by
  obtain ⟨w, rfl⟩ := List.get_of_mem hmem
  have ⟨w, h⟩ := fin.sur w
  obtain rfl := h.symm
  exact ⟨w, fin.extractor_agrees w⟩

def allMem (fin : Finite c) (n : Nat) : c n ∈ fin.ls := by
  rw [fin.extractor_agrees n]
  let this := (fin.extractor n)
  exact List.get_mem _ this.val this.prop

end equiv

def not_empty
    (fd : C.Finite c)
    : fd.ls ≠ [] :=
  List.ne_nil_of_mem $ fd.allMem 0

end C.Finite

instance [PartialOrder α] {c : C α} : Subsingleton (C.Finite c) where
  allEq a b := by
    have an := a.nodup
    have bn := b.nodup
    rcases a with ⟨al, oa, fa, ma, sa⟩
    rcases b with ⟨bl, ob, fb, mb, sb⟩
    dsimp at an bn
    obtain rfl : al = bl := by
      apply List.eq_of_perm_of_sorted ?_ oa ob
      apply (List.perm_ext_iff_of_nodup an bn).mpr fun el => ?_
      rw [List.mem_iff_get, List.mem_iff_get]
      constructor
      <;> rintro ⟨w, h⟩
      · obtain ⟨w, rfl⟩ := sa w
        specialize ma w
        obtain rfl := ma.trans h
        exists fb w
        exact (mb w).symm
      · obtain ⟨w, rfl⟩ := sb w
        specialize mb w
        obtain rfl := mb.trans h
        exists fa w
        exact (ma w).symm
    rw [C.Finite.mk.injEq]
    refine ⟨ rfl,
      (heq_eq_eq _ _).mpr
      $ funext
        (List.nodup_iff_injective_get.mp an
        $ (ma _).symm.trans $ mb ·)⟩

namespace Lub

variable [PartialOrder α] {c : C α} {hc : Chain c}

def finite.lemma_bound :
    {ls pf: _} →
    List.Pairwise LT.lt ls →
    c n ∈ ls →
    c n ≤ ls.getLast pf
  | [], pf, .nil, _ => False.elim $ pf rfl
  | hd :: [], _, .cons _ .nil, hmem => by simp_all
  | hd :: b :: tl, _, .cons hle cont, hmem => by
    obtain rfl|hmem := List.mem_cons.mp hmem
    · exact le_of_lt $ hle _ $ List.mem_of_mem_getLast? rfl
    · change _ ≤ (b :: tl).getLast _
      exact lemma_bound cont hmem
def finite (h : c.Finite)
  : Lub c (h.ls.getLast $ List.ne_nil_of_mem $ h.allMem 0) where
  lub_bound := fun n => finite.lemma_bound h.ordered (h.allMem n)
  lub_least x h' :=
    have : ∀ i ∈ h.ls, i ≤ x := fun i hv => by
      rcases h.memAll i hv with ⟨w, rfl⟩
      exact h' w
    this (h.ls.getLast _) $ List.getLast_mem _

def finite_mem
    (h : c.Finite)
    (hl : Lub c lub)
    : ∃ n, c n = lub :=
  h.memAll lub $ by
    obtain rfl := Lub.allEq (finite h) hl
    apply List.getLast_mem

end Lub

section

class FiniteDom (α : Type _) [PartialOrder α] where
  chain_fin (c : C α) (hc : Chain c) : c.Finite

instance [PartialOrder α] : CoeFun (FiniteDom α) (fun _ => (c : C α) → Chain c → c.Finite) where
  coe x := x.chain_fin

instance (priority := 500) {α} [PartialOrder α] [fd : FiniteDom α] [OrderBot α]  : Dom α where
  complete_lub c hc := Lub.finite $ fd c hc

def FiniteDom.complete_eq_chain_fin {α} [Dom α] {c : C α} {hc : Chain c} [fd : FiniteDom α]
    : complete c hc = (fd.chain_fin c hc).ls.getLast (C.Finite.not_empty _) :=
  Lub.allEq (complete_lub c hc) (Lub.finite $ fd c hc)

variable [ida : Dom α] {c : C α} {hc : Chain c}

def FiniteDom.complete_last
    [fd : FiniteDom α]
    (c : C α) hc
    : complete c hc
    = (fd.chain_fin c hc).ls.getLast (List.ne_nil_of_mem $ (fd.chain_fin c hc).allMem 0) :=
  Lub.allEq (complete_lub c hc) (Lub.finite (fd.chain_fin c hc))

open List in
section
def pw_mem
    [DecidableRel R]
    : {l : List α}
    → (a ∈ pwFilter R l)
    →  a ∈ l
  | [], h => h
  | x :: l, h' => by
    if h : ∀ y ∈ pwFilter R l, R x y then
      rw [pwFilter_cons_of_pos h, mem_cons] at h'
      rcases h' with rfl|h'
      · exact mem_cons_self a l
      · exact mem_cons_of_mem x $ pw_mem h'
    else
      rw [pwFilter_cons_of_neg h] at h'
      exact mem_cons_of_mem x $ pw_mem h'

def pw_lift
    [DecidableRel R]
    : {ls : List α}
    → List.Pairwise R' ls
    → Pairwise R' (pwFilter R ls)
  | [], .nil => .nil
  | x :: l, .cons hx hl =>
    if h : ∀ y ∈ pwFilter R l, R x y then
      pwFilter_cons_of_pos h ▸ .cons (hx · ∘ pw_mem) (pw_lift hl)
    else
      pwFilter_cons_of_neg h ▸ pw_lift hl

def pw_not_empty
    [DecidableRel R]
    : {ls : List α}
    → ls.pwFilter R ≠ []
    → ls ≠ []
  | [], h => False.elim $ h rfl
  | _ :: _, _ => List.noConfusion

def not_empty_pw
    [DecidableRel R]
    : {ls : List α}
    → ls ≠ []
    → ls.pwFilter R ≠ []
  | [], h => False.elim $ h rfl
  | [x], _ => List.noConfusion
  | x :: b :: l, _ =>
    if h : ∀ y ∈ pwFilter R (b :: l), R x y then
      pwFilter_cons_of_pos h ▸ List.noConfusion
    else
      pwFilter_cons_of_neg h ▸ not_empty_pw List.noConfusion

def pw_filter_last
    [DecidableRel R]
    : {ls : List α}
    → {nempty : ls.pwFilter R ≠ []}
    → (ls.pwFilter R).getLast nempty = ls.getLast (pw_not_empty nempty)
  | [], hne | [v], hne => rfl
  | x :: hb :: tl, hne => by
    if h : ∀ y ∈ pwFilter R (hb :: tl), R x y then
      have h := pwFilter_cons_of_pos h
      trans (x :: pwFilter R (hb :: tl)).getLast (h ▸ hne); congr
      rw [List.getLast_cons (not_empty_pw List.noConfusion)]
      exact pw_filter_last
    else
      have h := pwFilter_cons_of_neg h
      trans (pwFilter R (hb :: tl)).getLast (h ▸ hne); congr
      exact pw_filter_last
end

def sorted_of_nd_sorted
    {α} [PartialOrder α]
    : {ls : List α}
    → ls.Pairwise (· ≠ ·)
    → ls.Pairwise (· ≤ ·)
    → ls.Pairwise (· < ·)
  | [], .nil, .nil => .nil
  | _ :: _, .cons hne tne, .cons hle tle =>
    .cons (fun _ hmem => lt_of_le_of_ne (hle _ hmem) (hne _ hmem))
      $ sorted_of_nd_sorted tne tle

def nodup_mono_sorted
    [Preorder α] [PartialOrder β] [DecidableEq β]
    {f : α → β} (hMono : Monotone f)
    {la : List α}
    (hsort : List.Pairwise LT.lt la)
    : List.Sorted LT.lt (la.map f).dedup :=
  have sl : (List.map f la).Sorted (· ≤ ·) := by
    induction hsort
    · exact .nil
    case cons h _ ih =>
      refine .cons ?_ ih
      intro x hmem
      obtain ⟨x, h', rfl⟩ := List.mem_map.mp hmem
      apply hMono $ le_of_lt (h _ h')
  have sl := pw_lift (R := (· ≠ ·)) sl
  have nd := List.nodup_dedup $ la.map f
  sorted_of_nd_sorted nd sl

def FiniteDom.ls_map
    {α β}
    [PartialOrder α]
    [PartialOrder β]
    [DecidableEq β]
    [fda : FiniteDom α]
    [fdb : FiniteDom β]
    (c : C α) (hc : Chain c)
    (f : α → β)
    (hMono : Monotone f)
    : (fdb.chain_fin (c.map f) (hc.map hMono)).ls
    = ((fda.chain_fin c hc).ls.map f).dedup := by
  generalize chain_fin (c.map f) _ = fdb, chain_fin c hc = fda
  have an := fda.nodup
  have bn := fdb.nodup
  rcases fda with ⟨la, oa, fa, ma, sa⟩
  rcases fdb with ⟨lb, ob, fb, mb, sb⟩
  dsimp at *
  apply List.eq_of_perm_of_sorted ?perm ob (nodup_mono_sorted hMono oa)
  case perm =>
    apply (List.perm_ext_iff_of_nodup bn (List.nodup_dedup _)).mpr fun el => ?_
    rw [List.mem_dedup, List.mem_iff_get, List.mem_iff_get]

    have p₁ := (List.length_map la f)
    constructor
    <;> rintro ⟨w, h⟩
    · obtain ⟨w, rfl⟩ := sb w
      specialize mb w
      obtain rfl := mb.trans h
      exists cast (congr rfl p₁.symm) (fa w)
      rw [List.get_map]
      congr
      rw [←(ma w).symm]
      congr
      exact cast_heq (congr rfl p₁.symm) (fa w)
    · obtain ⟨w', p⟩ := sa (cast (congr rfl p₁) w)
      specialize ma w'
      subst h
      rw [List.get_map]
      exists fb w'
      exact (mb w').symm.trans
        $ congr (rfl (a := f))
        $ ma.trans
        $ congr rfl
        $ p.trans
        $ cast_eq_iff_heq.mpr
        $ (Fin.heq_ext_iff p₁).mpr rfl
end

section

variable [Dom D] [Dom E]

def Continous.finite [DecidableEq E] [dd : FiniteDom D] [de : FiniteDom E] {f : D → E} (fmono : Monotone f) : Continous f where
  mono := fmono
  preserves_lubs c hc := by
    repeat rw [FiniteDom.complete_eq_chain_fin]
    have eq' := FiniteDom.ls_map c hc f fmono
    have pnempty := C.Finite.not_empty (FiniteDom.chain_fin (c.map f) (Chain.map fmono))
    have pne' : ((FiniteDom.chain_fin c hc).ls.map f).dedup ≠ [] :=
      not_empty_pw $ fun x =>
        C.Finite.not_empty (FiniteDom.chain_fin c hc) $ List.map_eq_nil.mp x
    have : (FiniteDom.chain_fin (c.map f) (Chain.map fmono)).ls.getLast pnempty = ((FiniteDom.chain_fin c hc).ls.map f).dedup.getLast pne' := by congr
    simp only [this, List.dedup, pw_filter_last, List.getLast_map]

end

