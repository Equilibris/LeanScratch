import LeanScratch.LogicProof.PropLogic.Formula

namespace PLogic

def Formula.vMap (f : α → β) : Formula α → Formula β
  | .t => .t
  | .f => .f
  | .atom a => .atom (f a)
  | .conj a b => .conj (a.vMap f) (b.vMap f)
  | .disj a b => .disj (a.vMap f) (b.vMap f)
  | .neg v => .neg (v.vMap f)
  | .iff a b => .iff (a.vMap f) (b.vMap f)
  | .imp a b => .imp (a.vMap f) (b.vMap f)

def Formula.homo (form : Formula α) (f : α → β) : Prop := ∀ {base base'},
  (∀ x, base x = base' (f x)) → form.denote base = (form.vMap f |>.denote base')

inductive ForceInhabited (α : Type)
  | default
  | v : α → ForceInhabited α
deriving DecidableEq

instance : Inhabited (ForceInhabited α) := ⟨.default⟩

def Formula.injFI : Formula α → Formula (ForceInhabited α) := Formula.vMap ForceInhabited.v

theorem Formula.injFI.correct {form : Formula α} : form.homo ForceInhabited.v := fun hEq =>
  match form with
  | .t => rfl
  | .f => rfl
  | .atom a => hEq a
  | .neg v => by simp [denote, correct (form := v) hEq]
  | .conj a b | .disj a b | .iff a b | .imp a b => by
    simp [denote, correct (form := a) hEq, correct (form := b) hEq]

