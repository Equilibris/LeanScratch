import LeanScratch.Semantics.L1.Red

namespace L1


/-
  In L3, due to scoping of contexts, then semantic equivalence is very
  hard to figure out do to how varaibles are scoped.

  The big key here is the requirement of a context C[_].
-/

inductive CC (R : α → α → Prop) : ℕ → α → α → Prop
  | base : CC R 0 a a
  | cont : CC R n a b → R b c → CC R n.succ a c

theorem LoopPerm (hlt : n > 0) (x : CC R n a a) : ∀ k, ∃ z, CC R k a z := by
  intro k
  induction k
  · exact ⟨_, .base⟩
  · sorry

