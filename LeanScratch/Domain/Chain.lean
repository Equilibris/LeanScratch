import Mathlib.Order.Basic
import Mathlib.Data.Finset.Basic

namespace Dom

variable [ida : PartialOrder α]

structure Chain (α : Type _) [PartialOrder α] where
  gen : Nat → α
  chain (n : Nat) : gen n ≤ gen n.succ

def Chain.le_lift (c : Chain α) (h : a ≤ b)
    : c.gen a ≤ c.gen b := by
  induction h
  · exact ida.le_refl _
  case step ih =>
    exact ida.le_trans _ _ _ ih (c.chain _)

def Chain.rel (c : Chain α) a b
    : c.gen a ≤ c.gen b ∨ c.gen b ≤ c.gen a := by
  by_cases h : a ≤ b
  · exact .inl $ c.le_lift h
  · exact .inr $ c.le_lift $ Nat.le_of_not_ge h

structure Chain.finite (c : Chain α) : Type _ where
  ls : List α
  ordered : List.Pairwise ida.le ls
  allMem n : c.gen n ∈ ls
  memAll x (h : x ∈ ls) : ∃ n, c.gen n = x
