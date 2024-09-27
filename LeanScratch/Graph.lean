import Mathlib.Data.Rel

abbrev Graph α := Rel α α

namespace Graph

structure Path (α : Type*) :=
  selector : ℕ → Option α
  terminal : ∀ n, selector n = none → selector n.succ = none

def Path.shorten (x : Path α) : Path α where
  selector n := x.selector n.succ
  terminal n w := x.terminal (n + 1) w

abbrev FinPath := List

def Path.IsFin (x : Path α) := ∃ n, x.selector n = .none

inductive Path.length : Path α → ℕ → Prop
  | zero : p.selector 0 = .none → length p 0
  | cont { p : Path α } : (∃ v, p.selector 0 = .some v) → length p.shorten l → length p l.succ

def Path.length' (p : Path α) (h : Path.IsFin p) : ℕ :=
  let ⟨w, p⟩ := h
  sorry

/- #check Equiv -/

namespace Path

end Path

def Acyclic (g : Graph α) : Prop := ¬∃ x, Relation.TransGen g x x


