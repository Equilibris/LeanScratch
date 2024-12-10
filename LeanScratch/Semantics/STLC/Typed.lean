import LeanScratch.Semantics.STLC.Stx
import LeanScratch.Semantics.STLC.Red
import LeanScratch.Semantics.STLC.Red.Terminal
import LeanScratch.ListUtils
import Mathlib.Data.Rel
import LeanScratch.Relation

namespace STLC

open Stx

inductive TySpec : List Ty → Stx → Ty → Prop
  | bvar : Γ[idx]? = some ty → TySpec Γ (.bvar idx) ty

  | app : TySpec Γ fn (argTy ⇒ retTy) → TySpec Γ arg argTy
      → TySpec Γ (.app fn arg) retTy
  | abs : TySpec (ty :: Γ) body retTy
      → TySpec Γ (.abs ty body) (ty ⇒ retTy)

@[simp]
theorem TySpec_bvar : TySpec Γ (.bvar idx) ty ↔ Γ[idx]? = some ty := by
  constructor
  · rintro (h|_)
    exact h
  · intro h
    exact .bvar h

@[simp]
theorem TySpec_app : TySpec Γ (.app fn arg) ty ↔ 
  (∃ argTy, (TySpec Γ fn (argTy ⇒ ty) ∧ TySpec Γ arg argTy)) := by
  constructor
  · rintro (_|_)
    next argTy a b =>
    exact ⟨argTy, b, a⟩
  · intro ⟨_, a, b⟩
    exact .app a b

@[simp]
theorem TySpec_abs : TySpec Γ (.abs argTy body) (argTy ⇒ retTy) ↔ (TySpec (argTy :: Γ) body retTy) := by
  constructor
  · rintro (_|_|a)
    exact a
  · exact (.abs ·)

theorem TySpec_abs' : TySpec Γ (.abs argTy body) z ↔ ∃ retTy, (z = (argTy ⇒ retTy)) ∧ (TySpec (argTy :: Γ) body retTy) := by
  constructor
  · rintro (_|_|a)
    rename_i retTy
    exists retTy
  · rintro ⟨retTy, rfl, h⟩
    exact .abs h

theorem TySpec_unique (a : TySpec Γ i o₁) (b : TySpec Γ i o₂) : o₁ = o₂ :=
  match i with
  | .bvar id => by
    cases a
    cases b
    next ha hb =>
    exact (Option.some.injEq _ _).mp $ ha.symm.trans hb
  | .app fn arg => by
    cases a
    cases b
    next a argTy₁ fnTy₁ b argTy₂ fnTy₂ =>
    exact ((Ty.arr.injEq _ _ _ _).mp $ TySpec_unique fnTy₁ fnTy₂).2
  | .abs ty body => by
    cases a
    cases b
    next a ty₁ b ty₂ =>
    exact (Ty.arr.injEq _ _ _ _).mpr ⟨rfl, TySpec_unique ty₁ ty₂⟩


theorem bvarShift_maintain_gen
    (h : TySpec (Γ₂ ++ Γ) body ty₂)
    : TySpec (Γ₂ ++ Γ₁ ++ Γ) (bvarShift Γ₁.length Γ₂.length body) ty₂
    :=
  match body with
  | .bvar idx => by
    rw [List.append_assoc, bvarShift, TySpec_bvar]
    rw [TySpec_bvar] at h
    split
    next lt =>
      rw [List.getElem?_append lt]
      rw [List.getElem?_append lt] at h
      exact h
    next ge =>
      rw [not_lt] at ge
      rw [List.getElem?_append_right ge] at h
      rw [
        List.getElem?_append_right (ge.trans $ Nat.le_add_right _ _),
        Nat.sub_add_comm ge,
        List.getElem?_append_right (Nat.le_add_left Γ₁.length (idx - Γ₂.length)),
        add_tsub_cancel_right
      ]
      exact h
  | .abs ty body => by
    rw [List.append_assoc, bvarShift, Nat.succ_eq_add_one]
    cases h; next retTy h =>
    rw [←List.append_assoc]
    rw [←List.cons_append] at h

    exact .abs $ bvarShift_maintain_gen h

  | .app a b => by
    rw [bvarShift]
    cases h; next argTy ha hb =>

    exact .app (bvarShift_maintain_gen hb) (bvarShift_maintain_gen ha)

theorem bvarShift_maintain
    (h : TySpec Γ body ty₂)
    : (TySpec (Γ₁ ++ Γ) (bvarShift Γ₁.length 0 body) ty₂) := by
  change TySpec ([] ++ Γ₁ ++ Γ) (bvarShift Γ₁.length ([] : List Ty).length body) ty₂
  exact bvarShift_maintain_gen h

theorem TySpec_replace_gen
    (argTy : TySpec Γ arg x)
    (base : TySpec (Γ' ++ (x :: Γ)) body ty₁)
    : TySpec (Γ' ++ Γ) (body.replace (Γ'.length) arg) ty₁ :=
  match body with
  | .bvar idx => by
    rw [replace, replace.bvar, Nat.pred_eq_sub_one]
    split
    <;> rename_i heq
    <;> simp only [Nat.compare_eq_eq, Nat.compare_eq_gt, Nat.compare_eq_lt] at heq
    · cases base; next base =>
      rw [TySpec_bvar]
      rw [List.getElem?_append heq] at base ⊢
      exact base

    · rw [heq] at base
      cases base; next base =>
      rw [List.getElem?_append_right (Nat.le_refl Γ'.length), tsub_eq_zero_of_le (Nat.le_refl _),
        List.getElem?_cons_zero, Option.some.injEq] at base
      rw [base] at argTy
      change TySpec Γ _ _ at argTy
      exact bvarShift_maintain (Γ₁ := Γ') argTy

    · cases base; next base =>
      cases idx; contradiction; next n =>
      have heq : Γ'.length ≤ n := Nat.le_of_lt_succ heq
      rw [TySpec_bvar, add_tsub_cancel_right, List.getElem?_append_right heq]
      rw [
        List.getElem?_append_right $ heq.trans $ Nat.le_add_right n 1,
        Nat.sub_add_comm heq,
        List.getElem?_cons_succ
      ] at base

      exact base
  | .abs ty body => by
    rw [replace, Nat.succ_eq_add_one]
    cases base
    next rty₁ base =>
    rw [←List.cons_append] at base
    exact .abs $ TySpec_replace_gen argTy base
  | .app a b => by
    rw [replace]
    rw [TySpec_app] at base ⊢
    rcases base with ⟨ArgTy', hFn, hArg⟩

    exact ⟨_, TySpec_replace_gen argTy hFn, TySpec_replace_gen argTy hArg⟩

theorem TySpec_non_Red_Terminal
    (typed : TySpec Γ a ty) (r : ∀ b, ¬Red a b)
    : Terminal a :=
  match a with
  | .bvar id => by
    exact .nonEval .bvar
  | .abs ty body => by
    by_cases h : ∃ v, Red body v
    · rcases h with ⟨w, p⟩
      exfalso
      exact r (.abs ty w) (.congr p)
    · rw [not_exists] at h
      rcases typed with (_|_|bodyTyped)
      exact .abs $ TySpec_non_Red_Terminal bodyTyped h
  | .app a b => by
    by_cases hA : ∃ v, Red a v
    · rcases hA with ⟨w, p⟩
      exfalso
      exact r _ (.appl p)
    by_cases hB : ∃ v, Red b v
    · rcases hB with ⟨w, p⟩
      exfalso
      exact r _ (.appr p)
    rw [not_exists] at hA hB
    rcases typed with (_|⟨hFn, hArg⟩)
    have hA := (TySpec_non_Red_Terminal hFn hA)
    have hB := (TySpec_non_Red_Terminal hArg hB)
    cases hA
    · exfalso
      exact r _ .beta
    next h => exact .nonEval $ .app h hB

theorem Terminal_iff_non_Red (typed : TySpec Γ a ty) : (∀ b, ¬Red a b) ↔ Terminal a
  := ⟨TySpec_non_Red_Terminal typed, fun x _ => Terminal_not_Red x⟩

theorem TySpec_replace
    (hty₁ : TySpec Γ (.app (.abs x body) v) ty₁)
    : TySpec Γ (body.replace 0 v) ty₁ := by
  rw [TySpec_app] at hty₁
  rcases hty₁ with ⟨argTy, a, argTy⟩
  cases a
  next a =>
  change TySpec ([] ++ x :: Γ) _ _ at a
  exact TySpec_replace_gen argTy a

theorem TypePreservation (h : Red e₁ e₂) (hTy : TySpec Γ e₁ ty) : TySpec Γ e₂ ty :=
  match h with
  | .appl h => by
    cases hTy
    next bty hb ha =>
    exact .app (TypePreservation h ha) hb

  | .congr h => by
    cases hTy; next hTy =>
    rw [TySpec_abs]
    exact TypePreservation h hTy

  | .appr h => by
    cases hTy
    next bty hb ha =>
    exact .app ha (TypePreservation h hb)

  | .beta => TySpec_replace hTy

theorem Progress (hTy : TySpec Γ stx ty) : Terminal stx ∨ ∃ stx', Red stx stx' :=
  match stx with
  | .bvar id => .inl (.nonEval .bvar)
  | .abs ty body => by
    cases hTy; next retTy hTy =>
    by_cases h : ∃ body', Red body body'
    · rcases h with ⟨w, p⟩
      right
      use (.abs ty w)
      exact .congr p
    · rw [not_exists] at h
      exact .inl $ .abs $ TySpec_non_Red_Terminal hTy h
  | .app a b => by
    cases hTy
    next argTy arg fn =>
    rw [Terminal_app]
    cases Progress arg
    case inr h =>
      rcases h with ⟨w, p⟩
      exact .inr ⟨.app a w, .appr p⟩
    next hB =>
    rcases Progress fn with ((_|_)|_)
    · exact .inr ⟨_, .beta⟩
    case inr h =>
      rcases h with ⟨w, p⟩
      exact .inr ⟨.app w b, .appl p⟩
    case nonEval hA => exact .inl ⟨hA, hB⟩

theorem LongTypePreservation (spec : TySpec Γ e ty) (h : RedStar e e') : TySpec Γ e' ty := by
  induction h
  · exact spec
  next a ih => exact TypePreservation a ih

theorem Safety (spec : TySpec Γ e ty) (h : RedStar e e₁) : (Terminal e₁ ∨ ∃ e₂, Red e₁ e₂) := by
  induction h
  · exact Progress spec
  case tail b c cont hRed ih =>
    have tyB := LongTypePreservation spec cont
    cases' ih with h h
    · exact ((Terminal_iff_non_Red tyB).mpr h _ hRed).elim
    · exact Progress $ TypePreservation hRed tyB

/-- info: 'STLC.Safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Safety

theorem replace_gt_Γ (h : TySpec Γ s t) (hLe : Γ.length ≤ idx) : s.replace idx repl = s :=
  match s with
  | .bvar jdx => by
    cases h; next h =>
    have hLt := List.getElem?_lt_length h
    dsimp [replace, replace.bvar]
    split
    <;> rename_i h
    <;> simp only [Nat.compare_eq_eq, Nat.compare_eq_lt, Nat.compare_eq_gt] at h
    · rfl
    · subst h
      exact ((lt_self_iff_false _).mp (hLt.trans_le hLe)).elim
    · exact ((lt_self_iff_false _).mp ((hLt.trans_le hLe).trans h)).elim
  | .app a b => by
    cases h; next argTy ha hb =>
    simp only [replace, replace_gt_Γ ha hLe, replace_gt_Γ hb hLe]
  | .abs ty body => by
    cases h; next retTy h =>
    simp only [replace, Nat.succ_eq_add_one, abs.injEq, true_and]
    apply replace_gt_Γ h
    simpa only [List.length_cons, add_le_add_iff_right]

/-- info: 'STLC.replace_gt_Γ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms replace_gt_Γ 
end STLC

