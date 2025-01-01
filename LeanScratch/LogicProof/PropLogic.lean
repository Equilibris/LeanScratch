import Mathlib.Init.Set

inductive Formula (Atom : Type)
  | t | f

  | atom : Atom → Formula Atom
  | conj : Formula Atom → Formula Atom → Formula Atom
  | disj : Formula Atom → Formula Atom → Formula Atom
  | imp  : Formula Atom → Formula Atom → Formula Atom
  | iff  : Formula Atom → Formula Atom → Formula Atom
  | neg  : Formula Atom → Formula Atom

-- Didnt feel the course was well defined enough so see the following proof assistant
inductive Gentzen : (Set $ Formula Atom) → Formula Atom → Prop
  | t : Gentzen _ .t

  | holds : a ∈ ctx → Gentzen ctx a

  | conjIntro  : Gentzen ctx a →
                 Gentzen ctx b
      → Gentzen ctx (.conj a b)
  | disjlIntro : Gentzen ctx a
      → Gentzen ctx (.disj a b)
  | disjrIntro : Gentzen ctx b
      → Gentzen ctx (.disj a b)
  | impIntro   : Gentzen (ctx ∪ {a}) b
      → Gentzen ctx (.imp a b)
  | iffIntro   : Gentzen (ctx ∪ {a}) b →
                 Gentzen (ctx ∪ {b}) a
      → Gentzen ctx (.iff a b)
  | negIntro : Gentzen (ctx ∪ {a}) .f
      → Gentzen ct (.neg a)

  | conjElim : Gentzen (ctx ∪ {a, b}) v
      → .conj a b ∈ ctx → Gentzen ctx v

  | disjElim : Gentzen (ctx ∪ {a}) v →
               Gentzen (ctx ∪ {b}) v
      → .disj a b ∈ ctx → Gentzen ctx v

-- Theres an error in the notes on p9, showing the example deduction

-- We use lists and to make it easy to remove and read elements
-- We elimate into `Type` to avoid ax-K
inductive Sequent : List (Formula Atom) → List (Formula Atom) → Type
  -- This has the same effect as using sets
  | cycleL : Sequent (Γ ++ [hd]) Δ
      → Sequent ([hd] ++ Γ) Δ
  | cycleR : Sequent Γ (Δ ++ [hd])
      → Sequent Γ ([hd] ++ Δ)

  | wL : Sequent Γ Δ
      → Sequent (a :: Γ) Δ
  | wR : Sequent Γ Δ
      → Sequent Γ (a :: Δ)
  | cL : Sequent (a :: a :: Γ) Δ
      → Sequent (a :: Γ) Δ
  | cR : Sequent Γ (a :: a :: Δ)
      → Sequent Γ (a :: Δ)

  | triv : Sequent (a :: Γ) (a :: Δ)

  | fL : Sequent Γ (.t :: Δ)
      → Sequent (.f :: Γ) Δ
  | fR : Sequent (.t :: Γ) Γ
      → Sequent Γ (.f :: Δ)
  | tL : Sequent Γ Δ → Sequent (.t :: Γ) Δ
  | tR : Sequent Γ (.t :: Δ)

  | negL : Sequent Γ (a :: Δ)
      →  Sequent (.neg a :: Γ) Δ
  | negR : Sequent (a :: Γ) Δ
      →  Sequent Γ (.neg a :: Δ)

  | conjL : Sequent (a :: b :: Γ) Δ
      → Sequent (.conj a b :: Γ) Δ
  | conjR : Sequent Γ (a :: Δ) → Sequent Γ (b :: Δ)
      → Sequent Γ (.conj a b :: Δ)

  | disjL : Sequent (a :: Γ) Δ → Sequent (b :: Γ) Δ
      → Sequent (.disj a b :: Γ) Δ
  | disjR : Sequent Γ (a :: b :: Δ)
      → Sequent Γ (.disj a b :: Δ)

  | impL : Sequent Γ (a :: Δ) → Sequent (b :: Γ) Δ
      → Sequent (.imp a b :: Γ) Δ
  | impR : Sequent (a :: Γ) (b :: Δ)
      → Sequent Γ (.imp a b :: Δ)

  -- Ex 8
  | iffR  : Sequent (a :: Γ) (b :: Δ) →
            Sequent (b :: Γ) (a :: Δ)
      → Sequent Γ (.iff a b :: Δ)
  -- These might be able to be combided into one
  | iffL  : Sequent Γ (a :: Δ) → Sequent (b :: Γ) Δ
      → Sequent (.iff a b :: Γ) Δ
  | iffL' : Sequent (.iff b a :: Γ) Δ
      → Sequent (.iff a b :: Γ) Δ

  -- a ⊗ b is the same as ¬(a ↔ b) from a logical perspective
  -- so this then becomes simply combing these two into one

  -- See SN proof for STLC. Same method clears this I think
  | cut : Sequent Γ (a :: Δ) → Sequent (a :: Γ) Δ
      → Sequent Γ Δ

-- Just a simple shortcut to do Iff.mpr
abbrev Sequent.mprL : Sequent Γ (b :: Δ) → Sequent (a :: Γ) Δ
    → Sequent (.iff a b :: Γ) Δ := (.iffL' $ .iffL · ·)

example : Sequent [] [.disj (.imp a b) (.imp b a)] :=
  .disjR $ .impR $ .cycleR $ .impR $ .cycleR $ .triv
example : Sequent [] [.imp a a] := .impR .triv

namespace Exs

def Ex6_1 : Sequent [.neg $ .neg v] [v] := .negL $ .negR $ .triv
def Ex6_2 : Sequent [.conj a b] [.conj b a] :=
  .conjL $ .conjR (.cycleL .triv) .triv
def Ex6_3 : Sequent [.disj a b] [.disj b a] :=
  .disjR $ .disjL (.cycleR .triv) .triv

def Ex7_1 : Sequent [.conj (.conj a b) c] [.conj a (.conj b c)] :=
  .conjL $ .conjL $
    .conjR .triv $ .wL $ .conjR .triv $ .wL .triv

def Ex7_2 : Sequent [.conj (.disj a b) (.disj a c)] [.disj a (.conj b c)] :=
  .conjL $ .disjR $ .disjL .triv $ .cycleL $ .disjL .triv $
    .cycleR $ .conjR (.cycleL .triv) .triv

def Ex7_3 : Sequent [.neg (.disj a b)] [.conj (.neg a) (.neg b)] :=
  .negL $ .disjR $ .cycleR $ .cycleR $ .conjR
    (.negR .triv) (.negR $ .cycleR .triv)

-- Ex. falso
def Ex9_1 : Sequent [] [.imp (.conj a (.neg a)) b] :=
  .impR $ .conjL $ .cycleL $ .negL .triv

def falseTheorem : Sequent [] [.imp a b, a] :=  
  .impR $ .cycleR .triv

end Exs

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

