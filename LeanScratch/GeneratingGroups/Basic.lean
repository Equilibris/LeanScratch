import Mathlib.Data.Rel
import LeanScratch.GeneratingGroups.GG

namespace GGMod
inductive Rel (R : rTy α) : GG α → GG α → Prop
  | appUnit : Rel R (.app v .unit) (v)
  | unitApp : Rel R (.app .unit v) (v)
  | objInv : Rel R (.app (.obj a) (.inv a)) .unit
  | invObj : Rel R (.app (.inv a) (.obj a)) .unit
  | assoc : Rel R (.app (.app a b) c) (.app a (.app b c))
  | trans : Rel R a b → Rel R b c → Rel R a c
  | symm : Rel R a b → Rel R b a
  | refl : Rel R a a

  | base : R a b → Rel R a b
  | homo : Rel R a₁ a₂ → Rel R b₁ b₂ → Rel R (.app a₁ b₁) (.app a₂ b₂)

instance : Trans (Rel R) (Rel R) (Rel R) where trans a b := .trans a b

instance base (R : rTy α): Setoid (GG α) where
  r := Rel R
  iseqv := {
    refl := fun _ => .refl,
    trans := .trans,
    symm := .symm
  }

def RelSum (a b : α → β → Prop) (x : α) (y : β) := a x y ∨ b x y
end GGMod

open GGMod in
abbrev GGMod {α : Type u} (R : GG α → GG α → Prop) : Type u := Quotient (base R)

instance : Trans (@Eq (GGMod R)) (@Eq (GGMod R)) (@Eq (GGMod R)) where
  trans := by
    introv h₁ h₂
    exact h₁.trans h₂


namespace GGMod
def enter { R : rTy α} (x : GG α) : GGMod R :=
  Quotient.mk (base R) x

section
variable {α : Type u} {R : rTy α}

def app (a b : GGMod R) : GGMod R :=
  Quotient.lift₂ (fun a b => Quotient.mk (base R) (GG.app a b)) (by
    introv aeq beq
    simp only
    apply Quotient.sound'

    simp only [HasEquiv.Equiv, Setoid.r, base] at *
    exact .homo aeq beq
  ) a b

def obj (a : α) : GGMod R := Quotient.mk (base R) (.obj a)
def inv (a : α) : GGMod R := Quotient.mk (base R) (.inv a)
def unit : GGMod R := Quotient.mk (base R) .unit

@[simp]
theorem appUnit : app a unit = a := by
  unfold app
  induction a using Quotient.inductionOn
  apply Quotient.sound
  exact .appUnit
@[simp]
theorem unitApp : app unit a = a := by
  unfold app
  induction a using Quotient.inductionOn
  apply Quotient.sound
  exact .unitApp
@[simp]
theorem objInv : @app _ R (obj a) (inv a) = unit := by
  unfold app unit
  apply Quotient.sound
  exact .objInv
@[simp]
theorem invObj : @app _ R (inv a) (obj a) = unit := by
  unfold app
  apply Quotient.sound
  exact .invObj

/- theorem base (R a b) : a = b -/
end
@[simp]
theorem assoc : @app _ R (app a b) c = app a (app b c) := by
  unfold app
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  induction c using Quotient.inductionOn
  apply Quotient.sound
  exact .assoc

instance : Inhabited (GGMod R) := ⟨unit⟩
end GGMod

