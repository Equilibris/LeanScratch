import LeanScratch.LogicProof.FirstOrderLogic.Formula

namespace FOL

inductive Sequent {TNm : Type} {PNm : Type} {TA : TNm → ℕ} {PA : PNm → ℕ} :
    {Vars : Nat} → List (Formula Vars TA PA) → List (Formula Vars TA PA) → Type
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

  | iffR  : Sequent (a :: Γ) (b :: Δ) →
            Sequent (b :: Γ) (a :: Δ)
      → Sequent Γ (.iff a b :: Δ)

  | iffL  : Sequent Γ (a :: Δ) → Sequent (b :: Γ) Δ
      → Sequent (.iff a b :: Γ) Δ
  | iffL' : Sequent (.iff b a :: Γ) Δ
      → Sequent (.iff a b :: Γ) Δ

  | cut : Sequent Γ (a :: Δ) → Sequent (a :: Γ) Δ
      → Sequent Γ Δ

  | univL t : Sequent (a.β t :: Γ) Δ
      → Sequent (.univ a :: Γ) Δ 
  | univR   : Sequent Γ (a :: Δ)
      → Sequent Γ (.univ a :: Δ)
