import LeanScratch.LogicProof.PropLogic.Formula

namespace PLogic

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
