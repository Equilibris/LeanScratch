import Mathlib.Order.Basic
import Mathlib.Data.Finset.Basic

namespace Dom

variable [ida : PartialOrder α] [idb : PartialOrder β]

abbrev C (α : Type _) := Nat → α

class Chain (gen : C α) : Prop where
  chain (n : Nat) : gen n ≤ gen n.succ

instance {c : C α} : CoeFun (Chain c) (fun _ => (n : ℕ) → (c n ≤ c n.succ)) where
  coe x := x.chain

def Chain.le_lift (c : C α) [Chain c] (h : a ≤ b)
    : c a ≤ c b := by
  induction h
  · exact ida.le_refl _
  case step ih =>
    exact ida.le_trans _ _ _ ih (chain _)

def Chain.rel (c : C α) [Chain c] a b
    : c a ≤ c b ∨ c b ≤ c a := by
  by_cases h : a ≤ b
  · exact .inl $ le_lift c h
  · exact .inr $ le_lift c $ Nat.le_of_not_ge h

def C.map (c : C α) (f : α → β) : C β := f ∘ c

@[simp]
theorem C.map_id {c : C α} : c.map id = c := rfl

instance Chain.map {c : C α} {f : α → β} [ca : Chain c] (m : Monotone f) : Chain (c.map f) where
  chain n := m $ ca.chain n

def C.skip (k : Nat) (c : C α) : C α := fun n => c (k + n)
instance Chain.skip (k : Nat) {c : C α} [h : Chain c] : Chain (c.skip k) where
  chain n := h.chain (k + n)
