import Mathlib.Data.Rel
import Mathlib.Logic.Relation
import LeanScratch.GeneratingGroups.GG
import LeanScratch.GeneratingGroups.Basic

namespace GGMod

abbrev homo {R : rTy α} {R' : rTy β} (f : GGMod R → GGMod R') :=
  ∀ a b, f (.app a b) = .app (f a) (f b)

theorem homoComp {R₁ : rTy α} {R₂ : rTy β} {R₃ : rTy γ} {f : GGMod R₁ → GGMod R₂} {g : GGMod R₂ → GGMod R₃} (h₁ : homo f) (h₂ : homo g) : homo (g ∘ f) := by
  unfold homo Function.comp
  introv
  rw [h₁, h₂]

def Iso (R : rTy α) (R' : rTy β) : Prop := ∃f : GGMod R → GGMod R', homo f ∧ Function.Bijective f

scoped infix:20 " ≅ " => Iso

theorem isoRfl : R ≅ R := by
  use id
  constructor
  · unfold homo
    introv
    simp only [id]
  · exact Function.bijective_id

open Function in
theorem isoSymm {R : rTy α} {R' : rTy β} (h : R ≅ R') : R' ≅ R := by
  rcases h with ⟨w, p⟩
  use invFun w
  have rInv := rightInverse_invFun $ Bijective.surjective p.right
  have lInv := leftInverse_invFun  $ Bijective.injective p.right
  constructor
  · unfold homo
    introv
    change id (invFun w (a.app b)) = id ((invFun w a).app (invFun w b))
    have rInvId := RightInverse.id rInv
    have lInvId := LeftInverse.id lInv
    rw [lInvId.symm]
    have (a) : w (invFun w a) = a := by
      change _ = id a
      rw [←rInvId]
      simp only [comp_apply]

    unfold Function.comp
    conv =>
      rhs
      rw [p.left, this a, this b]
    rw [this]

  · apply bijective_iff_has_inverse.mpr
    use w
    constructor
    · exact rInv
    · exact lInv

theorem isoTrans {R₁ : rTy α} {R₂ : rTy β} {R₃ : rTy γ} (h₁₂ : R₁ ≅ R₂) (h₂₃ : R₂ ≅ R₃) : R₁ ≅ R₃ := by
  rcases h₁₂ with ⟨w₁₂, p₁₂⟩
  rcases h₂₃ with ⟨w₂₃, p₂₃⟩
  use w₂₃ ∘ w₁₂
  constructor
  · refine homoComp p₁₂.left p₂₃.left
  · apply Function.Bijective.comp p₂₃.right p₁₂.right

instance : @Trans (rTy α) (rTy β) (rTy γ) Iso Iso Iso := ⟨isoTrans⟩

/--
  Sometimes, proving statements over Setoids can be hard.
  This is a simple translation to the different statements needed.
-/
theorem Iso.Alt {R : rTy α} {R' : rTy β} :
    (∃ f : GG α → GG β, ∃ f' : GG β → GG α,
      (∀ {x y}, (Rel R) x y → (Rel R') (f x) (f y)) ∧
      (∀ {x y}, (Rel R') x y → (Rel R) (f' x) (f' y)) ∧
      (∀ {a b}, (Rel R') (f (.app a b)) (.app (f a) (f b))) ∧
      (∀ {x}, (Rel R) ((f' ∘ f) x) (x) ) ∧
      (∀ {x}, (Rel R') ((f ∘ f') x) (x) )
      ) → (R ≅ R') := by
  rintro ⟨f, f', fLaw, f'Law, homo, bijL, bijR⟩
  use fun x =>
    @Quotient.mk _ (base R') (f (@Quotient.out _ (base R) x))

  constructor
  · unfold GGMod.homo
    introv
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    rename_i a b
    simp only [app, Quotient.lift_mk, Quotient.eq]

    have := fLaw (@Quotient.mk_out _ (base R) (.app a b))
    have a := fLaw (@Quotient.mk_out _ (base R) a)
    have b := fLaw (@Quotient.mk_out _ (base R) b)
    simp only [Function.comp, HasEquiv.Equiv, Setoid.r] at bijR this ⊢

    exact .trans this (.trans homo (.homo a.symm b.symm))

  · apply Function.bijective_iff_has_inverse.mpr
    use fun x =>
      @Quotient.mk _ (base R) (f' (@Quotient.out _ (base R') x))
    constructor
    · simp only [Function.LeftInverse]
      introv
      induction x using Quotient.inductionOn
      rename_i x
      simp only [Quotient.eq]
      have inner :=  @Quotient.mk_out _ (base R) x
      have outer :=  @Quotient.mk_out _ (base R') (f (@Quotient.out _ (base R) (@Quotient.mk _ (base R) x) ))
      simp only [Function.comp, HasEquiv.Equiv, Setoid.r] at bijL inner outer ⊢

      exact .trans (f'Law outer) (.trans bijL inner)

    · simp only [Function.RightInverse, Function.LeftInverse]
      introv
      induction x using Quotient.inductionOn
      rename_i x
      simp only [Quotient.eq]
      have inner :=  @Quotient.mk_out _ (base R') x
      have outer :=  @Quotient.mk_out _ (base R) (f' (@Quotient.out _ (base R') (@Quotient.mk _ (base R') x) ))
      simp only [Function.comp, HasEquiv.Equiv, Setoid.r] at bijR inner outer ⊢

      exact .trans (fLaw outer) (.trans bijR inner)

end GGMod
