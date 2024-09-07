import Init.WF
import Mathlib.Logic.Relation


def sind.{u}
  {motive : ℕ → Sort u} (n : ℕ)
  (ind : (n : ℕ) → ((m : ℕ) → m < n → motive m) → motive n) : motive n :=
  sorry
  /- by -/
  /- induction n -/
  /- · apply ind 0 -/
  /-   introv h -/
  /-   contradiction -/
  /- case succ n a => -/
  /-   apply ind (n + 1) -/
  /-   introv -/

theorem ℕLtWF : WellFounded Nat.lt := by
  constructor
  introv
  induction a
  · constructor
    intro v h
    contradiction
  case succ n a =>
    constructor
    introv h
    cases Nat.lt_succ_iff_lt_or_eq.mp h
    next h =>
      sorry
    next h => rw [h]; exact a
  /- constructor -/
  /- introv -/
  /- induction a using Nat.strongInductionOn -/
  /- next n a => -/
  /- cases n -/
  /- · constructor -/
  /-   introv h -/
  /-   contradiction -/
  /- case succ n => -/
  /-   constructor -/
  /-   introv h -/
  /-   exact a  y h -/


