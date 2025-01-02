import LeanScratch.LogicProof.PropLogic.Formula
import Mathlib.Init.Set



/- def Formula.Sat (ctx : A → Prop) : Formula A → Prop -/
/-   | .atom v => ctx v -/

/-   | .neg v => v.Sat ctx → False -/

/-   | .conj a b => a.Sat ctx ∧ b.Sat ctx -/
/-   | .disj a b => a.Sat ctx ∨ b.Sat ctx -/

/-   | .imp a b => a.Sat ctx → b.Sat ctx -/
/-   | .iff a b => a.Sat ctx ↔ b.Sat ctx -/

/- def SatCol (ctx : A → Prop)  (S : Set (Formula A)) : Prop := ∀ v ∈ S, v.Sat ctx -/

/- def Valid       (S : Set (Formula A)) : Prop := ∀ ctx, SatCol ctx S -/
/- def Satisfiable (S : Set (Formula A)) : Prop := ∃ ctx, SatCol ctx S -/
/- -- Unsat triv -/
/- def Entails (S : Set (Formula A)) (f : Formula A) : Prop := -/
/-   ∀ ctx, SatCol ctx S → f.Sat ctx -/
/- infixl:30 " ⊨ " => Entails -/

/- def FEquiv (a b : Formula A) : Prop := ({a} ⊨ b) ∧ ({b} ⊨ a) -/
/- infixl:30 " ≃ " => FEquiv -/

/- namespace Exs -/

/- theorem Ex1 : ¬Satisfiable {.imp (.atom P) (.neg (.atom P))} := by -/
/-   intro ⟨interp, form⟩ -/
/-   simp only [SatCol, Set.mem_singleton_iff, forall_eq] at form -/
/-   dsimp [Formula.Sat] at form -/
/-   by_cases h : interp P -/
/-   · exact form h h -/
/-   · exact h (interp P) -/


/- end Exs -/

