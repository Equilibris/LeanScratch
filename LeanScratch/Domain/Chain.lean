import Mathlib.Order.Basic
import Mathlib.Data.Finset.Basic

namespace Dom

variable [ida : PartialOrder α] [idb : PartialOrder β]

abbrev C (α : Type _) := Nat → α

class Chain (gen : C α) : Prop where
  chain (n : Nat) : gen n ≤ gen n.succ

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

class C.finite (c : C α) : Type _ where
  ls : List α
  ordered : List.Pairwise ida.le ls
  allMem n : c n ∈ ls
  memAll x (h : x ∈ ls) : ∃ n, c n = x

def C.map (c : C α) (f : α → β) : C β := f ∘ c

instance Chain.map {c : C α} {f : α → β} [ca : Chain c] (m : Monotone f) : Chain (c.map f) where
  chain n := m $ ca.chain n
