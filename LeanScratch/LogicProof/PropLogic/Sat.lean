import LeanScratch.LogicProof.PropLogic.Sat.DPLL
import LeanScratch.LogicProof.PropLogic.VarMapper

namespace PLogic

instance Formula.satisfiable.dec [DecidableEq α] {form : Formula α} : Decidable (Formula.satisfiable form) :=
  match (dpll (form.injFI.transform .true).toClauseSet).toDecidable with
  | .isTrue p => .isTrue $ by
    rcases p with ⟨base, p⟩
    exact ⟨
      base ∘ .v,
      (Formula.injFI.correct (base' := base) (fun _ => rfl)).mpr
      $ (Formula.transform.tCorrect _).mpr
      $ (Formula.Dense.toClauseSet.correct _).mpr p
    ⟩
  | .isFalse p => .isFalse $ by
    dsimp [Formula.satisfiable]
    rw [not_exists] at p ⊢
    exact fun base v =>
      p (fun | .default => False | .v v => base v)
      $ (Formula.Dense.toClauseSet.correct _).mp
      $ (Formula.transform.tCorrect _).mp
      $ (Formula.injFI.correct (base := base) (fun _ => rfl)).mp v

instance Formula.tauto.dec [DecidableEq α] {form : Formula α} : Decidable (Formula.tauto form) :=
  match Formula.satisfiable.dec (form := form.neg) with
  | .isTrue v => .isFalse $ not_forall.mpr v
  | .isFalse v => .isTrue (not_not.mp $ not_exists.mp v ·)

