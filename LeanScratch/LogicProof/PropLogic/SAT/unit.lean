import LeanScratch.LogicProof.PropLogic.Clause
import LeanScratch.LogicProof.PropLogic.ClauseSet
import LeanScratch.LogicProof.PropLogic.SAT.fup
import LeanScratch.ListUtils

namespace PLogic

variable {α : Type} [DecidableEq α]

section defns

def Clause.unitize : Clause α → Option (α × Bool)
  | ⟨[x], []⟩ => .some ⟨x, .true⟩
  | ⟨[], [x]⟩ => .some ⟨x, .false⟩
  | _ => .none

def ClauseSet.extractUnits : ClauseSet α → List (α × Bool) := List.filterMap Clause.unitize

end defns

section correct

theorem Clause.unitize.correct {c : Clause α} (h : c.unitize = .some ⟨x, b⟩)
    : c.denote base = if b then ¬base x else base x := by
  simp [unitize] at h
  split at h
  case h_3 => exact Option.noConfusion h
  all_goals obtain ⟨rfl, rfl⟩ := (Option.some.injEq _ _).mp h
  all_goals simp [denote, denote.conjoin, denote.disjoin]


-- Thank fuck I came up with this theorem it just saved me so violently
theorem ClauseSet.extractUnits.correct
    {base : α → Prop} (h : holds base cs)
    : fup base cs.extractUnits = base :=
  match cs with
  | [] => rfl
  | hd :: tl => by
    rcases ClauseSet.holds_cons.mp h with ⟨hCurr, ih⟩
    clear h
    dsimp [extractUnits, List.filterMap_cons]
    have := ClauseSet.extractUnits.correct ih
    split
    · exact this
    next heq =>
      simp [Clause.unitize] at heq
      split at heq
      case h_3 => exact Option.noConfusion heq
      all_goals obtain ⟨rfl, rfl⟩ := (Option.some.injEq _ _).mpr heq
      all_goals ext x
      all_goals simp only [Clause.denote, Clause.denote.conjoin, and_true,
        Clause.denote.disjoin, imp_false, fup, if_false_left, extractUnits,
        Clause.denote.conjoin, or_false, true_implies, fup, if_true_left] at hCurr this ⊢
      all_goals rw [this]
      all_goals constructor
      all_goals by_contra!
      all_goals simp only [ne_eq, imp_iff_or_not,
        and_imp, imp_self, implies_true,
        Decidable.not_not, not_or] at this
      · rcases this with ⟨⟨_, h1⟩, h2⟩
        exact h2 h1
      · rcases this with ⟨h1, h2|rfl⟩
        exact h2 h1
        exact hCurr h1
      · rcases this with ⟨(h1|rfl), h2⟩
        exact h2 h1
        exact h2 hCurr
      · rcases this with ⟨h1, _, h2⟩
        exact h2 h1

end correct
