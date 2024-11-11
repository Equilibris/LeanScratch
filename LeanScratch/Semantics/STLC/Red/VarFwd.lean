import LeanScratch.Semantics.STLC.Stx
import LeanScratch.Semantics.STLC.Red.Beta
import LeanScratch.Semantics.STLC.Red.BetaCorrect
import LeanScratch.Semantics.STLC.Red.RefSet
import LeanScratch.Semantics.STLC.Red

namespace STLC

namespace Stx
theorem VarStasis_generalized
    (hNotRefSet : ∀ idx, ¬RefSet body (idx + n + 1))
    (hNotRepl : ∀ idx, ¬RefSet repl idx)
    {idx} : ¬RefSet (replace n body repl) (idx + n) :=
  match body with
  | .bvar id => by
    simp at hNotRefSet
    simp only [replace, replace.bvar, Nat.pred_eq_sub_one]
    split
    <;> intro h
    <;> rename_i heq
    <;> simp only [Nat.compare_eq_eq, Nat.compare_eq_gt, Nat.compare_eq_lt] at heq
    · cases h
      simp_all only [add_lt_iff_neg_right, not_lt_zero']
    · exact hNotRepl idx $ bvarShift_RefSet_rev h
    · simp at h
      have : 1 ≤ id := match id with | 0 => by contradiction; | n+1 => False.elim (hNotRefSet idx (congrFun (congrArg HAdd.hAdd h) 1))
      exact hNotRefSet idx $ (Nat.sub_eq_iff_eq_add this).mp h
  | .app a b => by
    simp only [RefSet_app, not_or, replace] at hNotRefSet ⊢
    exact ⟨
      VarStasis_generalized (fun idx => (hNotRefSet idx).1) hNotRepl,
      VarStasis_generalized (fun idx => (hNotRefSet idx).2) hNotRepl
    ⟩
  | .abs ty body => by
    intro h
    simp only [replace, Nat.succ_eq_add_one, RefSet_abs] at h hNotRefSet
    exact VarStasis_generalized hNotRefSet hNotRepl h

theorem VarStasis
    (h : ∀ idx, ¬RefSet (.app (.abs ty body) repl) idx) {idx}
    : ¬RefSet (body.β repl) idx := by
  simp only [RefSet_app, RefSet_abs, not_or] at h ⊢
  exact VarStasis_generalized (And.left $ h ·) (And.right $ h ·)

theorem VarFwd_generalized (h : RefSet (body.replace n repl) (idx + n))
    : RefSet (.abs ty' body) (idx + n) ∨ repl.RefSet idx :=
  match body with
  | .bvar id => by
    simp only [replace, replace.bvar, Nat.pred_eq_sub_one, RefSet_abs, RefSet_bvar] at h ⊢
    split at h
    <;> rename_i heq
    <;> simp only [Nat.compare_eq_eq, Nat.compare_eq_gt, Nat.compare_eq_lt] at heq
    · cases h
      simp_all only [add_lt_iff_neg_right, not_lt_zero']
    · have := bvarShift_RefSet_rev h
      exact .inr this
    · simp only [RefSet_bvar] at h
      have : 1 ≤ id := match id with | 0 => by contradiction | n+1 => Nat.le_add_left 1 _
      have := (Nat.sub_eq_iff_eq_add this).mp h
      simp_all only [add_tsub_cancel_right, le_add_iff_nonneg_left, zero_le, true_or]
  | .abs ty' body => by
    simp only [replace, Nat.succ_eq_add_one, RefSet_abs, add_assoc] at h
    rw [RefSet_abs]
    exact VarFwd_generalized h
  | .app a b => by
    simp only [replace, RefSet_app] at h ⊢
    rw [RefSet_dist]
    cases h
    <;> rename_i h
    <;> cases VarFwd_generalized h
    next h => exact .inl $ .inl h
    next h => exact .inr h
    next h => exact .inl $ .inr h
    next h => exact .inr h

/-- A β-reduction must always be a subset of the original referenced variables -/
theorem VarFwd (h : RefSet (body.β repl) idx) : RefSet (.app (.abs ty body) repl) idx := by
  rw [RefSet_app]
  exact VarFwd_generalized h
end Stx

open Stx in
theorem Red.VarFwd (r : Red a b) (next : RefSet b idx) : RefSet a idx :=
  match r with
  | .appl h => by
    rw [RefSet_app] at next ⊢
    match next with
    | .inl h' => exact .inl $ Red.VarFwd h h'
    | .inr h' => exact .inr h'
  | .congr h => by
    rw [RefSet_abs] at next ⊢
    exact Red.VarFwd h next
  | .appr h => by
    rw [RefSet_app] at next ⊢
    match next with
    | .inl h' => exact .inl h'
    | .inr h' => exact .inr $ Red.VarFwd h h'
  | .beta => STLC.Stx.VarFwd next
