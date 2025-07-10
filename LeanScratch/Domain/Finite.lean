import Mathlib.Order.Basic
import Mathlib.Data.Finset.Basic
import LeanScratch.Domain.Dom
import LeanScratch.Domain.Lub
import LeanScratch.Domain.Continous

namespace Dom

namespace C

variable [ida : PartialOrder α]

structure Finite (c : C α) : Type _ where
  ls : List α
  ordered : List.Pairwise ida.lt ls
  allMem n : c n ∈ ls
  memAll x (h : x ∈ ls) : ∃ n, c n = x

namespace Finite

variable {c : C α}

def nodup (f : Finite c) : f.ls.Nodup :=
  f.ordered.rec .nil
    (λ all_lt _ ih ↦ .cons (λ h ↦ (lt_self_iff_false _).mp $ all_lt _ h) ih)

noncomputable def extractor {x : α} (fin : Finite c) n (h : x ∈ fin.ls.get? n) : Nat :=
  Classical.choose (fin.memAll x $ List.get?_mem h)

theorem extractor.val {fin : Finite c} {h} : c (extractor (x := x) fin n' h) = x :=
  Classical.choose_spec (fin.memAll x $ List.get?_mem h)

def not_empty
    (fd : C.Finite c)
    : fd.ls ≠ [] :=
  List.ne_nil_of_mem $ fd.allMem 0

def ae.lemma
    {c : C α}
    [hc : Chain c]
    : {la lb : List α}
    → List.Pairwise LT.lt la
    → List.Pairwise LT.lt lb
    → (∀ (n : ℕ), c n ∈ la)
    → (∀ (n : ℕ), c n ∈ lb)
    → (∀ x ∈ la, ∃ n, c n = x)
    → (∀ x ∈ lb, ∃ n, c n = x)
    → la = lb
  | _, [], _, _, _, hm, _, _ | [], _, _, _, hm, _, _, _ => 
    False.elim $ (List.mem_nil_iff _).mp $ hm 0
  | ha :: [], hb :: _ :: _,
    .cons la pwla, .cons lb pwlb,
    ma, mb, _, h
  | hb :: _ :: _, ha :: [],
    .cons lb pwlb, .cons la pwla,
    mb, ma, h, _ => by
    simp_all only [List.not_mem_nil, implies_true, List.mem_cons,
      forall_eq_or_imp, forall_const, or_false, exists_const]
    rcases h with ⟨rfl, rfl, _⟩
    exact False.elim $ (lt_self_iff_false ha).mp lb.left
  | ha :: [], hb :: [],
    .cons la pwla, .cons lb pwlb,
    ma, mb, _, _ => by
    obtain rfl := (List.mem_singleton.mp $ ma 0).symm.trans (List.mem_singleton.mp $ mb 0)
    rfl
  | ha :: ca :: ta, hb :: cb :: tb,
    .cons la pwla, .cons lb pwlb,
    ama, amb, maa, mab => by
    obtain ⟨rfl, rfl⟩ := (List.cons.injEq _ _ _ _).mp $ ae.lemma
      (c := c.skip 1)
      pwla pwlb
      sorry sorry
      sorry sorry
    simp_all
    sorry
end C.Finite

/- instance {c : C α} [hc : Chain c] : Subsingleton (C.Finite c) where -/
/-   allEq a b := by -/
/-     rcases a with ⟨al, oa, ama, maa⟩ -/
/-     rcases b with ⟨bl, ob, amb, mab⟩ -/
/-     obtain rfl : al = bl := -/
/-       C.Finite.lemma oa ob ama amb maa mab -/
/-     rfl -/

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

