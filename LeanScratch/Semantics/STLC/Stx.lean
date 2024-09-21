import Mathlib.Data.Nat.PSub
import Mathlib.Data.Rel
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Util.WhatsNew

namespace STLC

inductive Ty
  | direct (id : ℕ)
  | arr (fn arg : Ty)

infixr:30 " ⇒ " => Ty.arr
prefix:30 "↑" => Ty.direct

inductive Stx
  | bvar (id : ℕ)
  | app  (fn arg : Stx)
  | abs  (ty : Ty) (body : Stx)

/- scoped prefix:30 "λ: " => Stx.abs -/
/- scoped prefix:30 "b:" => Stx.bvar -/
/- scoped infixl:30 " @ " => Stx.app -/

/- def analyze : Stx → LamTree -/
/-   | .bvar _ => .intro [] -/
/-   | .app a b => -/
/-     let .intro a := analyze a -/
/-     let .intro b := analyze b -/
/-     .intro (a ++ b) -/
/-   | .abs _ body => .intro [analyze body] -/

namespace Stx

/- inductive Ord : Stx → Stx → Prop -/
/-   | appl  : Ord a a' → Ord (.app a b ) (.app a' b) -/
/-   | appr  : Ord b b' → Ord (.app a b ) (.app a b') -/
/-   | congr : Ord a a' → Ord (.abs ty a) (.abs ty a') -/

def bvarShift (shift skip : ℕ) : Stx → Stx
  | .bvar n => .bvar $ if n < skip then n else n + shift
  | .app a b => .app (a.bvarShift shift skip) (b.bvarShift shift skip)
  | .abs ty body => .abs ty (body.bvarShift shift skip.succ)
def bvarUnShift (shift skip : ℕ) : Stx → Stx
  | .bvar n => .bvar $ if n - shift < skip then n else n - shift
  | .app a b => .app (a.bvarUnShift shift skip) (b.bvarUnShift shift skip)
  | .abs ty body => .abs ty (body.bvarUnShift shift skip.succ)

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


inductive RefSet : Stx → ℕ → Prop
  | appL : RefSet body idx → RefSet (.app body a) idx
  | appR : RefSet body idx → RefSet (.app a body) idx

  | abs : RefSet body idx.succ → RefSet (.abs ty body) idx

  | bvar : RefSet (.bvar idx) idx

@[simp]
theorem RefSet_abs : RefSet (.abs ty body) idx ↔ RefSet body (idx + 1) := by
  constructor
  <;> intro h
  · cases h; assumption
  · exact .abs h

@[simp]
theorem RefSet_app : RefSet (.app a b) idx ↔ (RefSet a idx ∨ RefSet b idx) := by
  constructor
  <;> rintro (h|h)
  · exact .inl h
  · exact .inr h
  · exact .appL h
  · exact .appR h

@[simp]
theorem RefSet_bvar : RefSet (.bvar idx) jdx ↔ idx = jdx := by
  constructor
  <;> intro h
  · cases h; rfl
  · rw [h]
    exact .bvar

example : RefSet (.abs (.direct 0) (.bvar 1)) 0 := .abs .bvar
example : ¬∃ n, RefSet (.abs (.direct 0) (.bvar 0)) n := by
  rintro ⟨n, _|_|(_|_)⟩
example : ¬∃ n, RefSet (.abs (.direct 0) (.bvar 0)) n := by
  intro ⟨n, x⟩ ; simp only [RefSet_abs, RefSet_bvar] at x

def replace.bvar (bvarId idx_shift : ℕ) (replace : Stx) : Stx :=
  match compare bvarId idx_shift with
  | .lt => .bvar bvarId
  | .eq => replace.bvarShift idx_shift 0
  | .gt => .bvar bvarId.pred

-- Replace also needs to add idx to every value within replace to ensure that the binders still point towards the right points
def replace (idx_shift : ℕ) (body replace : Stx) : Stx := match body with
  | .bvar n => Stx.replace.bvar n idx_shift replace
  | .app fn arg => .app (fn.replace idx_shift replace) (arg.replace idx_shift replace)
  | .abs ty v => .abs ty (v.replace idx_shift.succ replace)

def β (body repl : Stx) : Stx := (body.replace 0 repl)

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

theorem bvarShift_RefSet_rev (h : RefSet (body.bvarShift shift 0) (idx + shift)) : RefSet body idx :=
  bvarShift_RefSet_general_rev 0 h

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

example : RefSet (.abs ty (.bvar (n + 1))) n := .abs .bvar

lemma RefSet_dist : RefSet (.abs ty (.app a b)) idx ↔ RefSet (.abs ty a) idx ∨ RefSet (.abs ty b) idx := by
  constructor
  <;> intro h
  <;> simp only [RefSet_abs, RefSet_app] at h ⊢
  <;> exact h

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

mutual
inductive NonEval : Stx → Prop
  | bvar : NonEval (.bvar idx)
  | app (lhs : NonEval a) (rhs : Terminal b) : NonEval (.app a b)

inductive Terminal : Stx → Prop
  | abs (h : Terminal a) : Terminal (.abs ty a)
  | nonEval (h : NonEval a) : Terminal a
end

@[simp]
theorem Terminal_abs : Terminal (.abs ty a) ↔ Terminal a := by
  constructor
  <;> intro h
  · cases h
    next h => exact h
    next h => cases h
  · exact .abs h

@[simp]
theorem NonEval_bvar : NonEval (.bvar idx) ↔ True := by
  constructor <;> intro _
  · trivial
  · exact .bvar

@[simp]
theorem Terminal_bvar : Terminal (.bvar idx) ↔ True := by
  constructor <;> intro _
  · trivial
  · exact .nonEval .bvar

@[simp]
theorem Terminal_app : Terminal (.app a b) ↔ (NonEval a) ∧ (Terminal b) := by
  constructor
  <;> intro h
  · cases h; next h =>
    cases h; next a b =>
    exact ⟨a, b⟩
  · rcases h with ⟨a, b⟩
    exact .nonEval $ .app a b

@[simp]
theorem NonEval_app : NonEval (.app a b) ↔ (NonEval a) ∧ (Terminal b) := by
  constructor
  <;> intro h
  · cases h; next a b =>
    exact ⟨a, b⟩
  · rcases h with ⟨a, b⟩
    exact .app a b

end STLC.Stx
