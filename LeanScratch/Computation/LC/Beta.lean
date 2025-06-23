import LeanScratch.Computation.LC.Stx

namespace LC.Stx

inductive BV : Stx → Nat → Prop
  | bvar : BV (.bvar i) i
  | appl : BV a i → BV [l|a b] i
  | appr : BV b i → BV [l|a b] i
  | abs  : BV body (i + 1) → BV [l|λ. body] i

inductive FV : Stx → Nat → Prop
  | bvar : i ≠ j → FV (.bvar i) j
  | app  : FV a i → FV b i → FV [l|a b] i
  | abs  : FV body (i + 1) → FV [l|λ. body] i

def FV.bvarEq : FV (.bvar i) j = (i ≠ j) := propext ⟨
  fun | .bvar h => h,
  fun h => .bvar h⟩

def shift (shift skip : Nat) : Stx → Stx
  | .bvar n => .bvar $ if n < skip then n else n + shift
  | .app a b => .app (a.shift shift skip) (b.shift shift skip)
  | .abs body => .abs (body.shift shift skip.succ)

def unshift (shift skip : Nat) : Stx → Stx
  | .bvar n => .bvar $ if n < skip then n else n - shift
  | .app a b => .app (a.unshift shift skip) (b.unshift shift skip)
  | .abs body => .abs (body.unshift shift skip.succ)

abbrev replace.bvar (bvarId idx_shift : Nat) (replace : Stx) : Stx :=
  match compare bvarId idx_shift with
  | .lt => .bvar bvarId
  | .eq => replace.shift idx_shift 0
  | .gt => .bvar bvarId.pred

-- Replace also needs to add idx to every value within replace to ensure that the binders still point towards the right points
def replace (idx_shift : Nat) (body replace : Stx) : Stx := match body with
  | .bvar n => Stx.replace.bvar n idx_shift replace
  | .app fn arg => .app (fn.replace idx_shift replace) (arg.replace idx_shift replace)
  | .abs v => .abs (v.replace idx_shift.succ replace)

abbrev β : Stx → Stx → Stx := replace 0

theorem BVnFV : {s i : _} → (¬FV s i) = BV s i
  | .bvar i, j => propext ⟨
    fun x => by
      by_cases h : i = j
      · subst h
        exact .bvar
      · rw [FV.bvarEq] at x
        simp at x
        subst x
        exact (h rfl).elim,
    fun x y => by cases x; rcases y with (h|_); exact h rfl⟩
  | .abs _, _ => propext ⟨
    fun x => by sorry,
    fun x y => by cases x; cases y; sorry
  ⟩
  | .app _ _, _ => sorry

@[simp]
theorem shift_assoc (h : z ≤ n) : {body : Stx} → (body.shift n skip).shift m (z + skip) = body.shift (n + m) skip
  | .bvar _ => (Stx.bvar.injEq _ _).mpr $ by
    split
    all_goals simp_all only [ite_eq_left_iff, Nat.not_lt]
    any_goals split
    all_goals omega
  | .app _ _ => (Stx.app.injEq _ _ _ _).mpr ⟨shift_assoc h, shift_assoc h⟩
  | .abs _ => (Stx.abs.injEq _ _).mpr $
    shift_assoc h (skip := skip.succ)

@[simp]
theorem shift_unshift
    (hGt : skip  ≤ skip2)
    (hLt : skip2 ≤ n + skip)
    (hMN : m ≤ n)
    : {body : Stx} → (body.shift n skip).unshift m skip2 = body.shift (n - m) skip
  | .bvar _ => (Stx.bvar.injEq _ _).mpr $ by
    split
    all_goals simp_all only [ite_eq_left_iff, Nat.not_lt]
    any_goals split
    all_goals omega
  | .app _ _ => (Stx.app.injEq _ _ _ _).mpr ⟨shift_unshift hGt hLt hMN, shift_unshift hGt hLt hMN⟩
  | .abs _ => (Stx.abs.injEq _ _).mpr $
    shift_unshift (Nat.succ_le_succ hGt) (Nat.succ_le_succ hLt) hMN

@[simp]
theorem shift0 : {body : Stx} → body.shift 0 skip = body
  | .bvar id => by
    dsimp [shift]
    split <;> rfl
  | .abs _ => (Stx.abs.injEq _ _).mpr shift0
  | .app _ _ => (Stx.app.injEq _ _ _ _).mpr ⟨shift0, shift0⟩

@[simp]
theorem replace_bvar : replace n (.bvar n) x = shift n 0 x := by
  simp [replace, replace.bvar, Nat.compare_eq_eq.mpr]

@[simp]
theorem replace_bvar_gt (h : n < m) : replace m (.bvar n) x = .bvar n := by
  simp [replace, replace.bvar, Nat.compare_eq_lt.mpr h]

@[simp]
theorem replace_bvar_lt (h : m < n) : replace m (.bvar n) x = .bvar n.pred := by
  simp [replace, replace.bvar, Nat.compare_eq_gt.mpr h]

@[simp]
theorem replace_app : replace n (.app a b) x = .app (replace n a x) (replace n b x) := rfl

@[simp]
theorem replace_abs : replace n (.abs b) x = .abs (replace n.succ b x) := rfl

@[simp]
theorem FV_replace : {s : _} → (h : FV s i) → s.replace i repl = s.unshift 1 i
  | .bvar id, .bvar h => by
    dsimp [replace, unshift, replace.bvar]
    split
    <;> rename_i heq
    <;> simp [Nat.compare_eq_eq, Nat.compare_eq_gt, Nat.compare_eq_lt, h] at heq
    <;> split
    <;> simp_all only [ne_eq, bvar.injEq, Nat.not_lt]
    omega
  | .abs body, .abs h => (Stx.abs.injEq _ _).mpr $ FV_replace h
  | .app _ _, .app ha hb => (Stx.app.injEq _ _ _ _).mpr ⟨
    FV_replace ha,
    FV_replace hb
  ⟩

theorem FV_shift (hgt : s ≤ i) (hlt : i < sh + s) : {body : Stx} → FV (body.shift sh s) i
  | .bvar id => .bvar (by split <;> omega)
  | .abs _ => .abs (FV_shift (Nat.succ_le_succ hgt) (Nat.succ_lt_succ hlt))
  | .app _ _ => .app (FV_shift hgt hlt) (FV_shift hgt hlt)

@[simp]
theorem shift_replace : replace 0 (shift 1 0 x) y = x := by
  simp only [
    FV_replace $ FV_shift .refl (Nat.zero_lt_succ 0),
    Nat.le_refl, Nat.add_zero, Nat.zero_le, shift_unshift,
    Nat.sub_self, shift0]

@[simp]
theorem shift_replace' (h1 : skip ≤ k) (k2 : k ≤ n) : replace k (x.shift (n + 1) skip) y = shift n skip x := by
  rw [FV_replace]
  · rw [shift_unshift h1 _ (Nat.le_add_left 1 n)]
    rfl
    omega
  · apply FV_shift h1 (by omega)
