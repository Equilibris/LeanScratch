import LeanScratch.Semantics.STLC.Stx
import LeanScratch.Semantics.STLC.Red
import Mathlib.Data.Rel
import LeanScratch.Relation

namespace STLC

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

theorem TyUnique (a : TySpec Γ i o₁) (b : TySpec Γ i o₂) : o₁ = o₂ :=
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
    exact ((Ty.arr.injEq _ _ _ _).mp $ TyUnique fnTy₁ fnTy₂).2
  | .abs ty body => by
    cases a
    cases b
    next a ty₁ b ty₂ =>
    exact (Ty.arr.injEq _ _ _ _).mpr ⟨rfl, TyUnique ty₁ ty₂⟩

lemma List.getElem?_length {ls : List α} (h : ls[n]? = some v) : n < ls.length :=
  match ls with
  | .nil => Option.noConfusion h
  | .cons hd tl =>
    match n with
    | 0 => Nat.zero_lt_succ _
    | n+1 => by
      rw [List.length_cons, add_lt_add_iff_right]
      rw [List.getElem?_cons_succ] at h
      exact List.getElem?_length h

lemma List.eraseIdx_pre_k
    {k : Nat} {ls : List α} (shorter : k < n)
    (hv : (ls.eraseIdx n)[k]? = some z) : (ls[k]? = some z) := by
  induction ls, n using List.eraseIdx.induct generalizing k
  <;> dsimp [List.eraseIdx] at hv
  <;> (try contradiction)
  next hd tl n ih =>
    cases k
    · simp_all only [Nat.succ_eq_add_one, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
        List.length_cons, List.getElem?_eq_getElem, List.getElem_cons_zero, Option.some.injEq]
    next n' =>
      simp_all only [Nat.succ_eq_add_one, add_lt_add_iff_right, List.getElem?_cons_succ]

lemma List.eraseIdx_post_k
    {k : Nat} {ls : List α} (shorter : n ≤ k)
    (hv : (ls.eraseIdx n)[k]? = some z) : (ls[k+1]? = some z) := by
  induction ls, n using List.eraseIdx.induct generalizing k
  <;> dsimp [List.eraseIdx] at hv
  next => contradiction
  next head as =>
    rw [List.getElem?_cons_succ]
    exact hv
  next a as n ih =>
    rw [List.getElem?_cons_succ]
    cases k
    · contradiction
    next k =>
    rw [List.getElem?_cons_succ] at hv
    rw [Nat.succ_eq_add_one, add_le_add_iff_right] at shorter
    exact ih shorter hv

theorem ReverseBetaTypingX.bvar (id : ℕ) {Γ : List Ty} {arg : Stx} {argTy : Ty} {Γ' : List Ty} {n : ℕ} {ty₂ : Ty}
    (hArgTy : TySpec Γ arg argTy) (lookup : Γ'[n]? = some argTy)
    (repl : TySpec (Γ'.eraseIdx n ++ Γ) (Stx.replace.bvar id n arg) ty₂) : TySpec (Γ' ++ Γ) (.bvar id) ty₂ := by
  have lt := (List.getElem?_length lookup)
  dsimp [Stx.replace.bvar] at repl
  refine .bvar ?_
  split at repl
  <;> rename_i heq
  <;> simp [Nat.compare_eq_eq, Nat.compare_eq_gt, Nat.compare_eq_lt] at heq
  · -- ~~simple~~ LOL ABSOLUTELY NO.
    -- maybe false?
    sorry
  · -- ~~simple~~ LOL NO.
    rw [heq]
    rw [List.getElem?_eq_some] at lookup ⊢
    rcases lookup with ⟨p, v⟩
    simp
    have : n < Γ'.length + Γ.length := calc
      _ < Γ'.length := p
      _ ≤ _ := by linarith
    use this
    rw [List.getElem_append_left _ Γ p, v]
    sorry
  · rcases repl with (repl|_)
    rw [←List.eraseIdx_append_of_lt_length lt] at repl
    cases id; contradiction
    next idx =>
    rw [add_tsub_cancel_right] at repl
    exact List.eraseIdx_post_k (Nat.le_of_lt_add_one heq) repl

theorem ReverseBetaTypingX
    (hArgTy : TySpec Γ arg argTy) (lookup : Γ'[n]? = some argTy)
    (repl : TySpec (Γ'.eraseIdx n ++ Γ) (Stx.replace n body arg) ty₂)
    : TySpec (Γ' ++ Γ) body ty₂ :=
  match body with
  | .bvar id => ReverseBetaTypingX.bvar id hArgTy lookup repl
  | .app a b => by
    cases repl
    next hArg hFn =>
    exact .app (ReverseBetaTypingX hArgTy lookup hFn) (ReverseBetaTypingX hArgTy lookup hArg)
  | .abs ty body => by
    cases repl
    next retTy hrepl =>
    refine .abs ?_
    rw [←List.cons_append _ _ _]
    apply ReverseBetaTypingX (n := n+1) hArgTy
    · simp only [List.getElem?_cons_succ]
      exact lookup
    · rw [←List.cons_append _ _ _, ← List.eraseIdx_cons_succ] at hrepl
      exact hrepl

open Stx in
theorem bvarShift_maintain_gen
    (h : TySpec (Γ₂ ++ Γ₁ ++ Γ) (bvarShift Γ₁.length Γ₂.length body) ty₂)
    : TySpec (Γ₂ ++ Γ) body ty₂ :=
  match body with
  | .bvar idx => by
    simp only [List.append_assoc, bvarShift, TySpec_bvar] at h
    rw [TySpec_bvar]
    split at h
    next lt =>
      rw [List.getElem?_append lt]
      rw [List.getElem?_append lt] at h
      exact h
    next ge =>
      rw [not_lt] at ge
      rw [List.getElem?_append_right ge]
      rw [
        List.getElem?_append_right (ge.trans $ Nat.le_add_right _ _),
        Nat.sub_add_comm ge,
        List.getElem?_append_right (Nat.le_add_left Γ₁.length (idx - Γ₂.length)),
        add_tsub_cancel_right
      ] at h
      exact h
  | .abs ty body => by
    simp [bvarShift] at h
    cases h; next retTy h =>
    rw [←List.cons_append, ←List.append_assoc] at h

    exact .abs (bvarShift_maintain_gen h)

  | .app a b => by
    dsimp only [bvarShift] at h
    cases h; next argTy ha hb =>

    exact .app (bvarShift_maintain_gen hb) (bvarShift_maintain_gen ha)

open Stx in
theorem bvarShift_maintain
    (h : TySpec (Γ₁ ++ Γ) (bvarShift Γ₁.length 0 body) ty₂)
    : TySpec Γ body ty₂ := by
  change TySpec ([] ++ Γ₁ ++ Γ) (bvarShift Γ₁.length ([] : List Ty).length body) ty₂ at h
  exact bvarShift_maintain_gen h

open Stx in
theorem TySpec_replace_gen
    (argTy : TySpec Γ arg x)
    (base : TySpec (Γ' ++ (x :: Γ)) body ty₁)
    (repl : TySpec (Γ' ++ Γ) (body.replace (Γ'.length) arg) ty₂)
    : ty₁ = ty₂ :=
  match body with
  | .bvar idx => by
    simp [replace, replace.bvar] at repl
    split at repl
    <;> rename_i heq
    <;> simp only [Nat.compare_eq_eq, Nat.compare_eq_gt, Nat.compare_eq_lt] at heq
    · cases base; next base =>
      cases repl; next repl =>
      rw [List.getElem?_append heq] at repl base
      exact Option.some_inj.mp $ base.symm.trans repl
    · rw [heq] at base
      have repl := bvarShift_maintain repl
      clear heq idx
      cases base; next base =>
      simp only [List.length_append, List.length_cons, lt_add_iff_pos_right, add_pos_iff,
        zero_lt_one, or_true, List.getElem?_eq_getElem, lt_self_iff_false, not_false_eq_true,
        le_refl, tsub_eq_zero_of_le, List.getElem_append_right, List.getElem_cons_zero,
        Option.some.injEq] at base
      rw [base] at argTy
      exact TyUnique argTy repl
    · cases base; next base =>
      cases repl; next repl =>
      cases idx; contradiction; next n =>

      have heq : Γ'.length ≤ n := Nat.le_of_lt_succ heq

      rw [add_tsub_cancel_right, List.getElem?_append_right heq] at repl
      rw [
        List.getElem?_append_right $ heq.trans $ Nat.le_add_right n 1,
        Nat.sub_add_comm heq,
        List.getElem?_cons_succ
      ] at base

      exact Option.some_inj.mp $ base.symm.trans repl
  | .abs ty body => by
    simp only [replace, Nat.succ_eq_add_one] at repl
    cases base; cases repl
    next rty₁ base rty₂ repl =>
    rw [←List.cons_append] at repl base
    rw [TySpec_replace_gen argTy base repl]
  | .app a b => by
    simp only [TySpec_app, replace] at base repl
    rcases base with ⟨argTy₁, hFn₁, hArg₁⟩
    rcases repl with ⟨argTy₂, hFn₂, hArg₂⟩
    have hFn  := TySpec_replace_gen argTy hFn₁  hFn₂
    have hArg := TySpec_replace_gen argTy hArg₁ hArg₂

    rw [hArg] at hFn
    exact ((Ty.arr.injEq _ _ _ _).mp hFn).2

open Stx in
theorem TySpec_replace
    (hty₁ : TySpec Γ ((Stx.abs x body).app v) ty₁)
    (hty₂ : TySpec Γ (body.replace 0 v) ty₂)
    : ty₁ = ty₂ := by
  simp at hty₁
  rcases hty₁ with ⟨argTy, a, argTy⟩
  cases a
  next a =>
  change TySpec ([] ++ x :: Γ) _ _ at a
  apply TySpec_replace_gen argTy a
  sorry
  sorry
  sorry
  sorry
  /- match body with -/
  /- | .bvar idx => sorry -/
  /- | .abs ty body => by -/
  /-   simp [β, replace] at hty₂ -/
  /-   simp at hty₁ -/
  /-   rcases hty₁ with ⟨argTy, a, b⟩ -/
  /-   cases a -/
  /-   cases hty₂ -/
  /-   next a retTy hty₂ => -/
  /-   cases a -/
  /-   next retTy' a => -/
  /-   simp only [Ty.arr.injEq, true_and] -/
  /-   sorry -/
  /- | .app a b => by -/
  /-   simp [β, replace] at hty₂ -/
  /-   sorry -/
  /- by -/
  /- sorry -/

theorem TypePreservation (h : Red e₁ e₂) (hty₁ : TySpec Γ e₁ ty₁) (hty₂ : TySpec Γ e₂ ty₂) : ty₁ = ty₂ :=
  match h with
  | .appl h => by
    cases hty₁
    cases hty₂
    next bty₁ hb₁ ha₁ bty₂ hb₂ ha₂ =>

    exact ((Ty.arr.injEq _ _ _ _).mp $ TypePreservation h ha₁ ha₂).2

  | .appr h => by
    cases hty₁
    cases hty₂
    next bty₁ hb₁ ha₁ bty₂ hb₂ ha₂ =>

    exact ((Ty.arr.injEq _ _ _ _).mp $ TyUnique ha₁ ha₂).2

  | .beta => by
    cases hty₁
    next argTy _ v argTy hArgTy hfn =>
    rcases hfn with (_|_|hfn)
    dsimp [Stx.β] at hty₂

    change TySpec ([argTy] ++ Γ) _ _  at hfn
    change TySpec ([argTy].eraseIdx 0 ++ Γ) _ _  at hty₂

    refine TyUnique hfn (ReverseBetaTypingX hArgTy ?_ hty₂)
    simp only [List.length_singleton, zero_lt_one, List.getElem?_eq_getElem, List.getElem_cons_zero]
