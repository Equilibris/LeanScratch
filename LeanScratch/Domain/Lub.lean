import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import LeanScratch.Domain.Chain

namespace Dom

variable [ida : PartialOrder α] {c : Chain α}

structure Lub (c : Chain α) where
  lub : α
  lub_bound (n : Nat) : c.gen n ≤ lub
  lub_least (x : α) : (∀ n, c.gen n ≤ x) → lub ≤ x

instance {c : Chain α} : Subsingleton (Lub c) where
  allEq a b := by
    rcases a with ⟨a, a_bound, a_least⟩
    rcases b with ⟨b, b_bound, b_least⟩
    rw [Lub.mk.injEq]
    exact ida.le_antisymm _ _
      (a_least _ b_bound)
      (b_least _ a_bound)

def Lub.mono
    {d e : Chain α}
    (h : ∀ n, d.gen n ≤ e.gen n)
    {dlub : Lub d}
    {elub : Lub e}
    : dlub.lub ≤ elub.lub :=
  dlub.lub_least _ fun n =>
    ida.le_trans _ _ _
      (h n)
      (elub.lub_bound n)

def Lub.same
    (hSame : ∀ n, c.gen n = d)
    : Lub c where
  lub := d
  lub_bound := fun x => by rw [hSame]
  lub_least x h := by
    specialize hSame 0
    specialize h 0
    rw [←hSame]
    exact h

def Lub.contL
    {cskip : Chain α}
    (hCont : ∀ n, c.gen n = cskip.gen (n + a))
    (lub : Lub cskip)
    : Lub c where
  lub := lub.lub
  lub_bound := fun n => by rw [hCont]; exact lub.lub_bound _
  lub_least := fun x h =>
    lub.lub_least x fun n => by
      apply ida.le_trans _ _ _ (cskip.le_lift (Nat.le_add_right n a))
      rw [←hCont]
      exact h _
def Lub.contR
    {cskip : Chain α}
    (hCont : ∀ n, c.gen (n + a) = cskip.gen n)
    (lub : Lub cskip)
    : Lub c where
  lub := lub.lub
  lub_bound := fun n => by
    apply ida.le_trans _ _ _ (c.le_lift (Nat.le_add_right n a))
    rw [hCont]
    exact lub.lub_bound n
  lub_least := fun x h =>
    lub.lub_least x fun n => by rw [←hCont]; exact h _

def Lub.finite.lemma_bound :
    {ls pf: _} →
    List.Pairwise LE.le ls →
    c.gen n ∈ ls →
    c.gen n ≤ ls.getLast pf
  | [], pf, .nil, _ => False.elim $ pf rfl
  | hd :: [], _, .cons _ .nil, hmem => by simp_all
  | hd :: b :: tl, _, .cons hle cont, hmem => by
    obtain rfl|hmem := List.mem_cons.mp hmem
    · exact hle _ $ List.mem_of_mem_getLast? rfl
    · change _ ≤ (b :: tl).getLast _
      exact lemma_bound cont hmem
def Lub.finite (h : c.finite) : Lub c where
  lub := h.ls.getLast $ List.ne_nil_of_mem $ h.allMem 0
  lub_bound := fun n => finite.lemma_bound h.ordered (h.allMem n)
  lub_least x h' := 
    have : ∀ i ∈ h.ls, i ≤ x := fun i hv => by
      rcases h.memAll i hv with ⟨w, rfl⟩
      exact h' w
    this (h.ls.getLast _) $ List.getLast_mem _

def Lub.finite_mem
    (h : c.finite)
    (l : Lub c)
    : ∃ n, c.gen n = l.lub :=
  h.memAll l.lub $ by
    obtain rfl := Subsingleton.allEq (finite h) l
    apply List.getLast_mem

