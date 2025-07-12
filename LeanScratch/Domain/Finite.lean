import Mathlib.Order.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort
import LeanScratch.Domain.Dom
import LeanScratch.Domain.Lub
import LeanScratch.Domain.Continous
import LeanScratch.Fin2

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

  extractor (n : Nat) : Fin2 ls.length
  extractor_agrees (n : Nat) : c n = ls.getFin2 (extractor n)
  sur : Function.Surjective extractor

namespace Finite

section equiv

noncomputable def extractor.of
    {ls : List α}
    (allMem : ∀ n, c n ∈ ls)
    (n : Nat)
    : Fin2 ls.length :=
  Classical.choose $ Fin2.ofMem $ allMem n

theorem extractor_agrees.of
    {ls : List α}
    {allMem : ∀ n, c n ∈ ls}
    (n : Nat)
    : c n = ls.getFin2 (extractor.of allMem n) :=
  Classical.choose_spec (p := λ x ↦ c n = ls.getFin2 x) $ Fin2.ofMem $ allMem n

def nodup (f : Finite c) : f.ls.Nodup :=
  f.ordered.rec .nil
    (λ all_lt _ ih ↦ .cons (λ h ↦ (lt_self_iff_false _).mp $ all_lt _ h) ih)

theorem sur.of
    {ls : List α}
    {allMem : ∀ n, c n ∈ ls}
    (nodup : ls.Nodup)
    (memAll : (x : α) → x ∈ ls → ∃ n, c n = x)
    : Function.Surjective (extractor.of allMem) := fun res =>
  have ⟨w, p⟩ := memAll _ $ res.getFin2_mem
  ⟨w, Fin2.getFin2_Nodup_Injective nodup $ (extractor_agrees.of _).symm.trans p⟩

noncomputable def ofFinite' (f : Finite' c) : Finite c where
  ls := f.ls
  ordered := f.ordered
  extractor := extractor.of f.allMem
  extractor_agrees := extractor_agrees.of
  sur := sur.of f.nodup f.memAll

def memAll (fin : Finite c) (x : α) (hmem : x ∈ fin.ls) : ∃ n, c n = x := by
  obtain ⟨w, rfl⟩ := Fin2.ofMem hmem
  have ⟨w, h⟩ := fin.sur w
  obtain rfl := h.symm
  exact ⟨w, fin.extractor_agrees w⟩

def allMem (fin : Finite c) (n : Nat) : c n ∈ fin.ls := by
  rw [fin.extractor_agrees n]
  exact Fin2.getFin2_mem (fin.extractor n)

end equiv

def not_empty
    (fd : C.Finite c)
    : fd.ls ≠ [] :=
  List.ne_nil_of_mem $ fd.allMem 0

end C.Finite

instance [PartialOrder α] {c : C α} [hc : Chain c] : Subsingleton (C.Finite c) where
  allEq a b := by
    rcases a with ⟨al, oa, fa, ma, sa⟩
    rcases b with ⟨bl, ob, fb, mb, sb⟩
    have : ∀ n, al.getFin2 (fa n) = bl.getFin2 (fb n) := fun n =>
      (ma n).symm.trans (mb n)
    have : al = bl :=
      sorry
    stop
    rfl

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

instance [PartialOrder α] [fd : FiniteDom α] [OrderBot α] : Dom α where
  complete_lub c hc := Lub.finite $ fd c hc

variable [ida : Dom α] {c : C α} {hc : Chain c}

def FiniteDom.complete_last
    [fd : FiniteDom α]
    (c : C α) hc
    : complete c hc
    = (fd.chain_fin c hc).ls.getLast (List.ne_nil_of_mem $ (fd.chain_fin c hc).allMem 0) :=
  Lub.allEq (complete_lub c hc) (Lub.finite (fd.chain_fin c hc))

def FiniteDom.walker_lemma
    [db : Dom β]
    (f : α → β)
    (c : C α) (hc : Chain c)
    : (la : List α)
    → (lb : List β)
    → List.Pairwise LT.lt la
    → List.Pairwise LT.lt lb
    → (∀ (n : ℕ), c n ∈ la)
    → (∀ (n : ℕ), c.map f n ∈ lb)
    → (∀ x ∈ la, ∃ n, c n = x)
    → (∀ x ∈ lb, ∃ n, c.map f n = x)
    → lb = List.map f la :=
  sorry

/- def FiniteDom.ls_map -/
/-     [db : Dom β] -/
/-     [fda : FiniteDom α] -/
/-     [fdb : FiniteDom β] -/
/-     (c : C α) (hc : Chain c) -/
/-     (f : α → β) -/
/-     (hMono : Monotone f) -/
/-     : (fdb.chain_fin (c.map f) (hc.map hMono)).ls -/
/-     = (fda.chain_fin c hc).ls.map f := by -/
/-   have fda := chain_fin c hc -/
/-   have fdb := chain_fin (c.map f) (hc.map hMono) -/
/-   rcases fda with ⟨la, oa, ama, maa⟩ -/
/-   rcases fdb with ⟨lb, ob, amb, mab⟩ -/
/-   apply walker_lemma f c hc la lb -/


end

section

variable [Dom D] [Dom E]

def Continous.finite [dd : FiniteDom D] [de : FiniteDom E] {f : D → E} (fmono : Monotone f) : Continous.Helper f where
  mono := fmono
  preserves_lubs c hc := sorry

end

