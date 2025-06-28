import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import LeanScratch.Domain.Chain

namespace Dom

variable [ida : PartialOrder α] {c : C α} {hc : Chain c}

class Lub (c : C α) (lub : α) : Prop where
  lub_bound (n : Nat) : c n ≤ lub
  lub_least (x : α) : (∀ n, c n ≤ x) → lub ≤ x

def Lub.allEq
    (ha : Lub c a)
    (hb : Lub c b)
    : a = b := by
    rcases ha with ⟨a_bound, a_least⟩
    rcases hb with ⟨b_bound, b_least⟩
    exact ida.le_antisymm _ _
      (a_least _ b_bound)
      (b_least _ a_bound)

instance : Subsingleton (PSigma (Lub c)) where
  allEq a b := by
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    obtain rfl := Lub.allEq ha hb
    rfl

def Lub.mono
    {d e : C α}
    (h : ∀ n, d n ≤ e n)
    {hdlub : Lub d dlub}
    {helub : Lub e elub}
    : dlub ≤ elub :=
  hdlub.lub_least _ fun n =>
    ida.le_trans _ _ _
      (h n)
      (helub.lub_bound n)

def Lub.same
    (hSame : ∀ n, c n = d)
    : Lub c d where
  lub_bound := fun x => by rw [hSame]
  lub_least x h := by
    specialize hSame 0
    specialize h 0
    rw [←hSame]
    exact h

def Lub.contL
    {cskip : C α} {hcskip : Chain cskip}
    (hCont : ∀ n, c n = cskip (n + a))
    (hlub : Lub cskip lub)
    : Lub c lub where
  lub_bound := fun n => by rw [hCont]; exact hlub.lub_bound _
  lub_least := fun x h =>
    hlub.lub_least x fun n => by
      apply ida.le_trans _ _ _ (hcskip.le_lift (Nat.le_add_right n a))
      rw [←hCont]
      exact h _
def Lub.contR
    {cskip : C α}
    (hCont : ∀ n, c (n + a) = cskip n)
    (hlub : Lub cskip lub)
    : Lub c lub where
  lub_bound := fun n => by
    apply ida.le_trans _ _ _ (hc.le_lift (Nat.le_add_right n a))
    rw [hCont]
    exact hlub.lub_bound n
  lub_least := fun x h =>
    hlub.lub_least x fun n => by rw [←hCont]; exact h _

def Lub.finite.lemma_bound :
    {ls pf: _} →
    List.Pairwise LE.le ls →
    c n ∈ ls →
    c n ≤ ls.getLast pf
  | [], pf, .nil, _ => False.elim $ pf rfl
  | hd :: [], _, .cons _ .nil, hmem => by simp_all
  | hd :: b :: tl, _, .cons hle cont, hmem => by
    obtain rfl|hmem := List.mem_cons.mp hmem
    · exact hle _ $ List.mem_of_mem_getLast? rfl
    · change _ ≤ (b :: tl).getLast _
      exact lemma_bound cont hmem
def Lub.finite (h : c.finite)
  : Lub c (h.ls.getLast $ List.ne_nil_of_mem $ h.allMem 0) where
  lub_bound := fun n => finite.lemma_bound h.ordered (h.allMem n)
  lub_least x h' :=
    have : ∀ i ∈ h.ls, i ≤ x := fun i hv => by
      rcases h.memAll i hv with ⟨w, rfl⟩
      exact h' w
    this (h.ls.getLast _) $ List.getLast_mem _

def Lub.finite_mem
    (h : c.finite)
    (hl : Lub c lub)
    : ∃ n, c n = lub :=
  h.memAll lub $ by
    obtain rfl := Lub.allEq (finite h) hl
    apply List.getLast_mem

