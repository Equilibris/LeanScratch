import LeanScratch.Semantics.STLC.Stx
import Mathlib.Data.Rel
import LeanScratch.Relation

namespace STLC

inductive Red : Stx → Stx → Prop
  | appl : Red a a' → Red (.app a b) (.app a' b)
  | appr : Red b b' → Red (.app a b) (.app a b')
  | congr : Red a a' → Red (.abs ty a) (.abs ty a')
  | beta : Red (.app (.abs _ body) v) (body.β v)

@[simp]
theorem Red_abs : Red (.abs ty body) a ↔ ∃ body', (Red body body') ∧ a = .abs ty body' := by
  constructor
  <;> intro h
  · cases h; next body' h =>
    use body'
  · rcases h with ⟨body', h, rfl⟩
    exact .congr h

open Stx in
theorem Red.VarFwd (r : Red a b) (next : RefSet b idx ) : RefSet a idx :=
  match r with
  | .appl h => by
    simp only [RefSet_app] at next ⊢
    match next with
    | .inl h' => exact .inl $ Red.VarFwd h h'
    | .inr h' => exact .inr h'
  | .congr h => by
    rw [RefSet_abs] at next ⊢
    exact Red.VarFwd h next
  | .appr h => by
    simp only [RefSet_app] at next ⊢
    match next with
    | .inl h' => exact .inl h'
    | .inr h' => exact .inr $ Red.VarFwd h h'
  | .beta => STLC.Stx.VarFwd next

abbrev RedStar := Relation.ReflTransGen Red
abbrev RedPlus := Relation.TransGen Red

mutual
theorem Terminal_not_Red (terminal : Stx.Terminal a) : ¬Red a b := fun h =>
  match h with
  | .appl h => by
    rw [Stx.Terminal_app] at terminal
    rcases terminal with ⟨a, _⟩
    exact NonEval_not_Red a h
  | .appr h => by
    rw [Stx.Terminal_app] at terminal
    rcases terminal with ⟨_, a⟩
    exact Terminal_not_Red a h
  | .congr h => by
    rw [Stx.Terminal_abs] at terminal
    exact Terminal_not_Red terminal h
  | .beta => by rcases terminal with (_|_|_|_)
theorem NonEval_not_Red (terminal : Stx.NonEval a) : ¬Red a b := fun h =>
  match h with
  | .appl h => by
    rw [Stx.NonEval_app] at terminal
    rcases terminal with ⟨a, _⟩
    exact NonEval_not_Red a h
  | .appr h => by
    rw [Stx.NonEval_app] at terminal
    rcases terminal with ⟨_, a⟩
    exact Terminal_not_Red a h
  | .congr h => by
    cases terminal
  | .beta => by rcases terminal with (_|_|_)
end

end STLC

