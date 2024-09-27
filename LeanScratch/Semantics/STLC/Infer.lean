import LeanScratch.Semantics.STLC.Typed

namespace STLC

def infer (Γ : List Ty) : Stx → Option Ty
  | .bvar idx => Γ[idx]?
  | .abs ty body => (infer (ty :: Γ) body).map (.arr ty ·)
  | .app a b => do
    let (.arr argTy retTy) ← infer Γ a | none
    let argTy' ← infer Γ b
    if argTy = argTy' then some retTy else none

theorem infer_TySpec : infer Γ stx = .some ty ↔ TySpec Γ stx ty := match stx with
  | .bvar idx => by simp only [infer, TySpec_bvar]
  | .abs argTy body => by
    constructor
    <;> simp only [infer, Option.map_eq_some', forall_exists_index, and_imp]
    · rintro retTy h rfl
      simp only [TySpec_abs]
      exact infer_TySpec.mp h
    · intro h
      cases h
      next retTy hBody =>
      use retTy
      simp only [and_true]
      exact infer_TySpec.mpr hBody
  | .app a b => by
    constructor
    <;> simp only [TySpec_app, infer, Option.bind_eq_bind, forall_exists_index, and_imp]
    · intro x
      obtain ⟨_|_, ap⟩ : ∃ v, infer Γ a = v := exists_eq'
      <;> simp only [ap, Option.none_bind, Option.some_bind] at x
      split at x
      case h_2 => contradiction
      obtain ⟨_|_, bp⟩ : ∃ v, infer Γ b = v := exists_eq'
      <;> simp only [bp, Option.some_bind, ite_some_none_eq_some, Option.none_bind] at x
      rcases x with ⟨rfl, rfl⟩
      exact ⟨_, infer_TySpec.mp ap , infer_TySpec.mp bp⟩
    · intro _ ha hb
      rw [infer_TySpec.mpr ha, infer_TySpec.mpr hb]
      simp only [Option.some_bind, ↓reduceIte]

/-- info: 'STLC.infer_TySpec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms infer_TySpec

@[simp]
theorem infer_bvar : infer Γ (.bvar idx) = Γ[idx]? := rfl

@[simp]
theorem infer_abs : infer Γ (.abs ty body) = (infer (ty :: Γ) body).map (.arr ty ·) := rfl

/- @[simp] -/
/- theorem infer_app : infer Γ (.app a b) = (infer (ty :: Γ) body).map (.arr ty ·) := rfl -/

