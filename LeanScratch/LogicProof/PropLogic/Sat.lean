import LeanScratch.LogicProof.PropLogic.Sat.DPLL

namespace PLogic

inductive ForceInhabited (α : Type)
  | default
  | v : α → ForceInhabited α
deriving DecidableEq

instance : Inhabited (ForceInhabited α) := ⟨.default⟩

def Formula.injFI : Formula α → Formula (ForceInhabited α)
  | .t => .t
  | .f => .f
  | .atom a => .atom (.v a)
  | .conj a b => .conj a.injFI b.injFI
  | .disj a b => .disj a.injFI b.injFI
  | .neg v => .neg v.injFI
  | .iff a b => .iff a.injFI b.injFI
  | .imp a b => .imp a.injFI b.injFI

theorem Formula.injFI.correct {form : Formula α} (hEq : ∀ v, base v = base' (.v v))
    : form.denote base = form.injFI.denote base' := match form with
  | .t => rfl
  | .f => rfl
  | .atom a => hEq a
  | .neg v => by simp [denote, correct (form := v) hEq]
  | .conj a b | .disj a b | .iff a b | .imp a b => by
    simp [denote, correct (form := a) hEq, correct (form := b) hEq]

instance Formula.satisfiable.dec [DecidableEq α] {form : Formula α} : Decidable (Formula.satisfiable form) :=
  match (dpll (form.injFI.transform .true).toClauseSet).toDecidable with
  | .isTrue p => .isTrue $ by
    rcases p with ⟨base, p⟩
    refine ⟨base ∘ .v, ?_⟩
    apply (Formula.injFI.correct (base' := base) (fun _ => rfl)).mpr
    apply (Formula.transform.tCorrect _).mpr
    apply (Formula.Dense.toClauseSet.correct _).mpr
    exact p
  | .isFalse p => .isFalse $ by
    dsimp [Formula.satisfiable]
    rw [not_exists] at p ⊢
    intro base v
    apply p (fun | .default => False | .v v => base v)
    apply (Formula.Dense.toClauseSet.correct _).mp
    apply (Formula.transform.tCorrect _).mp
    apply (Formula.injFI.correct (base := base) (fun _ => rfl)).mp
    exact v

instance Formula.tauto.dec [DecidableEq α] {form : Formula α} : Decidable (Formula.tauto form) :=
  match Formula.satisfiable.dec (form := form.neg) with
  | .isTrue v => .isFalse $ not_forall.mpr v
  | .isFalse v => .isTrue (not_not.mp $ not_exists.mp v ·)

