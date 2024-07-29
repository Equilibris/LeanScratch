import LeanScratch.GeneratingGroups.Iso

namespace GGMod
def K : GGMod.rTy α := fun _ _ => True
def E : GGMod.rTy Empty := fun _ _ => False

theorem K.KillSingular { α } : @K α ≅ E := by
  use fun _ => GGMod.unit
  constructor
  · unfold GGMod.homo
    introv
    simp only [GGMod.appUnit]
  · apply Function.bijective_iff_has_inverse.mpr
    use fun _ => GGMod.unit
    simp only [Function.LeftInverse, Function.RightInverse]
    constructor
    <;> introv
    <;> induction x using Quotient.inductionOn
    <;> apply Quotient.sound
    <;> simp only [HasEquiv.Equiv, Setoid.r]
    · exact .base True.intro
    · rename_i x
      induction x
      · exact .refl
      · trivial
      · trivial
      case app a_ih b_ih =>
        exact .symm (.trans (.homo a_ih.symm b_ih.symm) .appUnit)
end GGMod
