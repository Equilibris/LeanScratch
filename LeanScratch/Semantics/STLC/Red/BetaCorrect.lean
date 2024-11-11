import LeanScratch.Semantics.STLC.Stx
import LeanScratch.Semantics.STLC.Red.RefSet
import LeanScratch.Semantics.STLC.Red.Beta

namespace STLC.Stx

def bvarUnShift (shift skip : ℕ) : Stx → Stx
  | .bvar n => .bvar $ if n - shift < skip then n else n - shift
  | .app a b => .app (a.bvarUnShift shift skip) (b.bvarUnShift shift skip)
  | .abs ty body => .abs ty (body.bvarUnShift shift skip.succ)

/-- Proof of correctness for bvarShift's shifting -/
@[simp]
theorem bvarUnShift_bvarShift : bvarUnShift shift skip (bvarShift shift skip s) = s := by
  induction s generalizing shift skip
  <;> simp only [bvarUnShift, Nat.succ_eq_add_one, abs.injEq, true_and, bvar.injEq, app.injEq]
  case bvar id => split <;> split <;> omega
  case app fn_ih arg_ih => exact ⟨fn_ih, arg_ih⟩
  case abs body_ih => exact body_ih

example : bvarShift k 0 (.bvar n) = (.bvar (n + k))                     := by simp only [bvarShift, not_lt_zero', ↓reduceIte]
example : bvarShift k (.succ n) (.bvar 0) = (.bvar 0)                   := by simp only [bvarShift, Nat.succ_eq_add_one, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, ↓reduceIte]
example : bvarShift k 0 (.abs ty (.bvar 0)) = (.abs ty $ .bvar 0)       := by simp only [bvarShift, Nat.succ_eq_add_one, zero_add, zero_lt_one, ↓reduceIte]
example : bvarShift k 0 (.abs ty (.bvar 1)) = (.abs ty $ .bvar (1 + k)) := by simp only [bvarShift, Nat.succ_eq_add_one, zero_add, lt_self_iff_false, ↓reduceIte]

@[simp]
theorem bvarShift.inv : Stx.bvarShift 0 n z = z := by
  induction z generalizing n
  <;> dsimp only [Stx.bvarShift]
  · split <;> rfl
  case app fn_ih arg_ih =>
    simp only [Stx.app.injEq]
    exact ⟨fn_ih, arg_ih⟩
  case abs ty body ih=>
    simp only [Stx.abs.injEq, true_and]
    exact ih

theorem bvarShift_RefSet_general (h : RefSet body (idx + skip)) : RefSet (body.bvarShift shift skip) (idx + shift + skip) :=
  match body with
  | .bvar id => by
    simp at h
    rw [h]
    clear h
    simp only [bvarShift, add_lt_iff_neg_right, not_lt_zero', ↓reduceIte, RefSet_bvar]
    exact Nat.add_right_comm idx skip shift
  | .abs ty body => by
    simp_all [bvarShift]
    exact bvarShift_RefSet_general h
  | .app a b => by
    simp only [RefSet_app, bvarShift] at h ⊢
    cases h
    next h => exact .inl $ bvarShift_RefSet_general h
    next h => exact .inr $ bvarShift_RefSet_general h

theorem bvarShift_RefSet (h : RefSet body idx) : RefSet (body.bvarShift shift 0) (idx + shift) := bvarShift_RefSet_general h

theorem bvarShift_RefSet_general_rev
    skip (h : RefSet (body.bvarShift shift skip) (idx + shift + skip))
    : RefSet body (idx + skip) :=
  match body with
  | .bvar id => by
    simp_all [bvarShift]
    split at h
    next lt => -- contradiction
      rw [h] at lt
      simp_all only [add_lt_iff_neg_right, not_lt_zero']
    · have : id = idx + skip := by
        rw [add_assoc, add_comm shift, ←add_assoc] at h
        exact Nat.add_right_cancel h
      rw [this]
  | .abs ty body => by
    simp only [bvarShift, Nat.succ_eq_add_one, RefSet_abs] at h ⊢
    rw [add_assoc] at h
    exact bvarShift_RefSet_general_rev (skip + 1) h
  | .app a b => by
    simp only [bvarShift, RefSet_app] at h ⊢
    cases h
    next h => exact .inl $ bvarShift_RefSet_general_rev skip h
    next h => exact .inr $ bvarShift_RefSet_general_rev skip h

example : RefSet (.abs ty (.bvar (n + 1))) n := .abs .bvar

theorem bvarShift_RefSet_rev (h : RefSet (body.bvarShift shift 0) (idx + shift)) : RefSet body idx :=
  bvarShift_RefSet_general_rev 0 h
