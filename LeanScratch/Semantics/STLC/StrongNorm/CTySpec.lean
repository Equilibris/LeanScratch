import LeanScratch.Semantics.STLC.Typed
import LeanScratch.Semantics.STLC.Infer

namespace STLC

-- I finally see why proof-relevance is useful.
-- Damn that took me a long time to get
-- This does not work due to how AC is defined on Prop...
-- And (=) does only produce a Prop

-- C for constructive
inductive CTySpec : List Ty → Stx → Ty → Type
  | bvar : Γ[idx]? = some ty → CTySpec Γ (.bvar idx) ty

  | app : CTySpec Γ fn (argTy ⇒ retTy) → CTySpec Γ arg argTy
      → CTySpec Γ (.app fn arg) retTy
  | abs : CTySpec (argTy :: Γ) body retTy
      → CTySpec Γ (.abs argTy body) (argTy ⇒ retTy)

theorem CTySpec_TySpec (h : CTySpec Γ s ty) : TySpec Γ s ty := by
  induction h
  · exact .bvar (by assumption)
  · exact .app (by assumption) (by assumption)
  · exact .abs (by assumption)

def build (h : infer Γ s = some ty) : CTySpec Γ s ty :=
  match s with
  | .bvar idx => .bvar (by simpa only)
  | .abs ty body =>
    match h' : infer (ty :: Γ) body with
    | .none => by
      -- contra
      simp [infer, h'] at h
    | .some x => by
      simp only [infer, h', Option.map_some', Option.some.injEq] at h
      subst h
      exact .abs (build h')
  | .app a b =>
    match ha : infer Γ a, hb : infer Γ b with
    | some aTy, some bTy => by
      simp only [infer, ha, hb, Option.bind_eq_bind, Option.some_bind] at h
      split at h
      <;> (try split at h)
      <;> (try contradiction)
      next h' =>
      have := ((Option.some.injEq _ _).mp h)
      subst this h'
      exact .app (build ha) (build hb)
    | none, _ => by
      -- contra
      simp only [infer, ha, Option.bind_eq_bind, Option.none_bind] at h
    | some (.direct _), none
    | some (.arr _ _),  none => by
      simp only [infer, ha, hb, Option.bind_eq_bind, Option.none_bind, Option.some_bind] at h

def TySpec_CTySpec (h : TySpec Γ s ty) : CTySpec Γ s ty := build (infer_TySpec.mpr h)

theorem CTySpec_unique (h₁ : CTySpec Γ s o₁) (h₂ : CTySpec Γ s o₂) : o₁ = o₂ :=
  TySpec_unique (CTySpec_TySpec h₁) (CTySpec_TySpec h₂)

theorem CTySpec_singleton (a b : CTySpec Γ s ty) : a = b :=
  match s with
  | .bvar _ => by cases a; cases b; rfl
  | .abs _ _ => by
    cases a; cases b; next a b =>
    rw [CTySpec_singleton a b]
  | .app _ _ => by
    cases a; cases b; next a₁ b₁ _ a₂ b₂ =>
    obtain rfl := CTySpec_unique a₁ a₂
    rw [CTySpec_singleton a₁ a₂, CTySpec_singleton b₁ b₂]

instance : Subsingleton (CTySpec Γ s ty) := ⟨CTySpec_singleton⟩

