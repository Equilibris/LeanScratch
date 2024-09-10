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

namespace Stx

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

def maxV : Stx → Option ℕ
  | .bvar n => .some n
  | .abs _ b => b.maxV >>= Nat.ppred
  | .app a b => match a.maxV, b.maxV with
    | .some a, .some b => .some $ max a b
    | .none, .some a | .some a, .none => .some a
    | .none, .none => .none     -- This can be less patterns but this simplifies simps

def minV : Stx → Option ℕ
  | .bvar n => .some n
  | .abs _ b => b.minV >>= Nat.ppred
  | .app a b => match a.minV, b.minV with
    | .some a, .some b => .some $ min a b
    | .none, .some a | .some a, .none => .some a
    | .none, .none => .none     -- This can be less patterns but this simplifies simps

example : minV (.abs (.direct 0) $ .bvar 0) = none   := by simp only [minV, Option.bind_eq_bind, Option.some_bind, Nat.ppred_zero]
example : minV (.abs (.direct 0) $ .bvar 1) = some 0 := by simp only [minV, Option.bind_eq_bind, Option.some_bind, Nat.ppred_succ]
example : minV (.app (.bvar 2) (.bvar 1)) = some 1   := by simp only [minV, Nat.one_le_ofNat, min_eq_right]
example (h : body.minV = .none) : minV (.abs (.direct 0) body) = none := by
  simp only [minV, Option.bind_eq_bind, Option.bind_eq_none, Nat.ppred_eq_none]
  intro n x
  simp_all only
example (h : body.minV = .some 0) : minV (.abs (.direct 0) body) = none := by
  simp only [minV, Option.bind_eq_bind, Option.bind_eq_none, Nat.ppred_eq_none]
  intro n x
  simp_all only [Option.some.injEq]
example (h : body.minV = .some (n + 1)) : ∃ w, minV (.abs (.direct 0) body) = some w := by
  simp only [minV, Option.bind_eq_bind]
  use n
  rw [h]
  simp only [Option.some_bind, Nat.ppred_succ]

theorem minVEitherZOrNone (h : (abs ty body).minV = none) : body.minV = none ∨ body.minV = some 0 := by
  simp_all only [minV]
  induction body
  case bvar id => simp_all only [minV, Option.bind_eq_bind, Option.some_bind, Nat.ppred_eq_none,
    or_true]
  case app fn arg fn_ih arg_ih =>
    simp_all only [minV, Option.bind_eq_bind, Option.bind_eq_none, Nat.ppred_eq_none]
    split
    <;> simp_all only [Option.some.injEq, forall_eq', Nat.zero_min, or_true, implies_true,
      Nat.min_zero, Nat.min_eq_zero_iff]
  case abs ty' body _ =>
    by_contra!
    rcases this with ⟨a, b⟩
    simp only [minV, Option.bind_eq_bind, Option.bind_eq_none, Nat.ppred_eq_none, ne_eq,
      not_forall, Classical.not_imp] at h a b
    rcases a with ⟨w, pEqSome, nez⟩
    simp only [pEqSome, Option.some_bind, Nat.ppred_eq_some, Nat.succ_eq_add_one] at h
    obtain ⟨w', p'⟩ := Nat.exists_eq_succ_of_ne_zero nez
    rw [p'] at h
    specialize h w' (by simp only [Nat.succ_eq_add_one])
    simp_all only [Nat.succ_eq_add_one, zero_add, Option.bind_eq_bind, Option.some_bind,
      Nat.ppred_succ, Option.some.injEq, one_ne_zero, or_true, false_implies, not_true_eq_false]
theorem maxVEitherZOrNone (h : (abs ty body).maxV = none) : body.maxV = none ∨ body.maxV = some 0 := by
  simp_all only [maxV]
  induction body
  case bvar id => simp_all only [maxV, Option.bind_eq_bind, Option.some_bind, Nat.ppred_eq_none,
    or_true]
  case app fn arg fn_ih arg_ih =>
    simp_all only [maxV, Option.bind_eq_bind, Option.bind_eq_none, Nat.ppred_eq_none]
    split
    <;> simp_all only [Option.some.injEq, forall_eq', Nat.zero_min, or_true, implies_true,
      Nat.min_zero, Nat.min_eq_zero_iff]
  case abs ty' body _ =>
    by_contra!
    rcases this with ⟨a, b⟩
    simp only [maxV, Option.bind_eq_bind, Option.bind_eq_none, Nat.ppred_eq_none, ne_eq,
      not_forall, Classical.not_imp] at h a b
    rcases a with ⟨w, pEqSome, nez⟩
    simp only [pEqSome, Option.some_bind, Nat.ppred_eq_some, Nat.succ_eq_add_one] at h
    obtain ⟨w', p'⟩ := Nat.exists_eq_succ_of_ne_zero nez
    rw [p'] at h
    specialize h w' (by simp only [Nat.succ_eq_add_one])
    simp_all only [Nat.succ_eq_add_one, zero_add, Option.bind_eq_bind, Option.some_bind,
      Nat.ppred_succ, Option.some.injEq, one_ne_zero, or_true, false_implies, not_true_eq_false]
theorem maxVAppSome (h : (abs ty body).maxV = some m) : body.maxV = some m.succ := by
  simp only [maxV, Option.bind_eq_bind] at h
  by_cases hz : ∃ w, body.maxV = some w
  · rcases hz with ⟨w, p⟩
    simp_all only [Option.some_bind, Nat.ppred_eq_some, Nat.succ_eq_add_one]
  · simp only [not_exists] at hz
    rw [Option.eq_none_iff_forall_not_mem.mpr hz] at h
    contradiction

mutual
theorem bvarShiftNoneSkip shift skip (h : body.maxV = none) : (bvarShift shift skip body) = body :=
  match body with
  | .bvar idx => by simp only [bvarShift, maxV] at *
  | .app a b => by
    simp_all only [bvarShift, maxV]
    split at h <;> simp_all
    next ha hb =>
    exact ⟨bvarShiftNoneSkip shift skip ha, bvarShiftNoneSkip shift skip hb⟩
  | .abs ty body => 
    match maxVEitherZOrNone h with
    | .inl a => by
      simp only [bvarShift, Nat.succ_eq_add_one, abs.injEq, true_and]
      exact bvarShiftNoneSkip shift (skip + 1) a
    | .inr a => by
      simp only [bvarShift, Nat.succ_eq_add_one, abs.injEq, true_and]
      exact bvarShiftSomeSkip shift (skip + 1) a (Nat.zero_lt_succ skip)

theorem bvarShiftSomeSkip shift skip (h : body.maxV = some m) (h' : m < skip): (bvarShift shift skip body) = body :=
  match body with
  | .bvar idx => by
    simp only [maxV, Option.some.injEq] at h
    simp only [bvarShift, h, bvar.injEq, ite_eq_left_iff, not_lt, add_right_eq_self]
    intro hz
    exfalso
    exact Nat.le_lt_asymm hz h'
  | .app a b => by
    simp only [maxV] at h
    split at h
    <;> simp only [Option.some.injEq] at h
    <;> simp only [bvarShift, app.injEq]
    next a b hFn hArg =>
      obtain ⟨ha, hb⟩ := Nat.max_lt.mp (calc
        _ = m := h
        _ < skip := h')

      exact ⟨
        bvarShiftSomeSkip shift skip hFn  ha,
        bvarShiftSomeSkip shift skip hArg hb
      ⟩
    next a hFn hArg =>
      rw [←h] at h'
      exact ⟨
        bvarShiftNoneSkip shift skip hFn,
        bvarShiftSomeSkip shift skip hArg h'
      ⟩
    next a hFn hArg =>
      rw [←h] at h'
      exact ⟨
        bvarShiftSomeSkip shift skip hFn h',
        bvarShiftNoneSkip shift skip hArg
      ⟩
  | .abs ty body => by
    simp only [bvarShift, Nat.succ_eq_add_one, abs.injEq, true_and]
    exact bvarShiftSomeSkip shift (skip + 1) (maxVAppSome h) (Nat.succ_lt_succ h')
end

/-- info: 'STLC.Stx.bvarShiftSomeSkip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bvarShiftSomeSkip
/-- info: 'STLC.Stx.bvarShiftNoneSkip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bvarShiftNoneSkip

theorem empty_bvarShift (hMin : s.minV = .none) (hMax : s.maxV = .none) : (bvarShift shift n s).minV = .none ∧ (bvarShift shift n s).maxV = .none :=
  match s with
  | .bvar id => by contradiction
  | .abs ty body | .app a b => by
    simp only [bvarShiftNoneSkip shift n hMax]
    exact ⟨hMin, hMax⟩

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

/- def replace.bvar (bvarId idx_shift : ℕ) (replace : Stx) : Stx := -/
/-   if idx_shift = bvarId then replace.bvarShift idx_shift 0 -/
/-   else .bvar bvarId -/

/- -- Replace also needs to add idx to every value within replace to ensure that the binders still point towards the right points -/
/- def replace (idx_shift : ℕ) (body replace : Stx) : Stx := match body with -/
/-   | .bvar n => Stx.replace.bvar n idx_shift replace -/
/-   | .app fn arg => .app (fn.replace idx_shift replace) (arg.replace idx_shift replace) -/
/-   | .abs ty v => .abs ty (v.replace idx_shift.succ replace) -/

/- theorem replace_with_non_RefSet {body : Stx} (h : ¬RefSet body idx) : body.replace idx repl = body := -/
/-   match body with -/
/-   | .bvar jdx => by -/
/-     simp only [replace, replace.bvar, ite_eq_right_iff] -/
/-     rintro rfl -/
/-     exfalso -/
/-     exact h .bvar -/
/-   | .abs ty body => by -/
/-     simp only [replace, Nat.succ_eq_add_one, abs.injEq, true_and, RefSet_abs] at h ⊢ -/
/-     exact replace_with_non_RefSet h -/
/-   | .app a b => by -/
/-     simp only [replace, app.injEq, RefSet_app, not_or] at h ⊢ -/
/-     exact ⟨replace_with_non_RefSet h.1, replace_with_non_RefSet h.2⟩ -/

/- def decAbove (n : ℕ) : Stx → Stx -/
/-   | .bvar idx    => .bvar $ if idx > n then idx.pred else idx -/
/-   | .abs ty body => .abs ty $ body.decAbove n.succ -/
/-   | .app a b     => .app (a.decAbove n) (b.decAbove n) -/

/- theorem minVDist {a b : Stx} (h : (a.app b).minV = some bot) : -/
/-     (a.minV = .none ∨ (∃ am, a.minV = some am ∧ bot ≤ am)) ∧ -/
/-     (b.minV = .none ∨ (∃ bm, b.minV = some bm ∧ bot ≤ bm)) := by -/
/-   simp only [minV] at h -/
/-   split at h -/
/-   <;> simp only [Option.some.injEq] at h -/
/-   next a b ha hb => -/
/-     rcases min_eq_iff.mp h with (⟨_, _⟩|⟨_, _⟩) -/
/-     <;> refine ⟨.inr ⟨_, ha, ?_⟩ , .inr ⟨_, hb, ?_⟩⟩ -/
/-     <;> simp_all only [min_eq_left_iff, le_refl] -/
/-   next ha hb => -/
/-     exact ⟨.inl ha, .inr ⟨_, hb, Nat.le_of_eq (Eq.symm h)⟩⟩ -/
/-   next ha hb => -/
/-     exact ⟨.inr ⟨_, ha, Nat.le_of_eq (Eq.symm h)⟩, .inl hb⟩ -/

/- mutual -/
/- theorem replace_maxVLtNone {body : Stx} (h : body.maxV = none) : body.replace idx repl = body := -/
/-   match body with -/
/-   | .bvar n => by simp only [maxV] at h -/
/-   | .app a b => by -/
/-     simp [maxV, replace] at h ⊢ -/
/-     split at h <;> try contradiction -/
/-     next ha hb => -/
/-     exact ⟨replace_maxVLtNone ha, replace_maxVLtNone hb⟩ -/
/-   | .abs ty body => by -/
/-     simp only [replace, Nat.succ_eq_add_one, abs.injEq, true_and] -/
/-     cases maxVEitherZOrNone h -/
/-     case inl h => -/
/-       exact replace_maxVLtNone h -/
/-     case inr h => -/
/-       exact replace_maxVLtSome h (Nat.zero_lt_succ idx) -/

/- theorem replace_maxVLtSome {body : Stx} (h : body.maxV = some mV) (lt : mV < idx) : body.replace idx repl = body := -/
/-   match body with -/
/-   | .bvar n => by -/
/-     simp only [maxV, Option.some.injEq] at h -/
/-     simp only [replace, replace.bvar, ite_eq_right_iff] -/
/-     intro idxEqN -/
/-     rw [←h,idxEqN] at lt -/
/-     exfalso -/
/-     exact (lt_self_iff_false n).mp lt -/
/-   | .app a b => by -/
/-     simp only [replace, app.injEq] -/
/-     simp only [maxV] at h -/
/-     split at h -/
/-     <;> simp only [Option.some.injEq] at h -/
/-     next av bv hA hB => -/
/-       obtain ⟨hALe, hBLe⟩ := Nat.max_le.mp (Nat.le_of_eq h) -/
/-       exact ⟨ -/
/-         replace_maxVLtSome hA (Nat.lt_of_le_of_lt hALe lt), -/
/-         replace_maxVLtSome hB (Nat.lt_of_le_of_lt hBLe lt) -/
/-       ⟩ -/
/-     next av hA hB => -/
/-       rw [h] at hB -/
/-       exact ⟨replace_maxVLtNone hA, replace_maxVLtSome hB lt⟩ -/
/-     next bv hA hB => -/
/-       rw [h] at hA -/
/-       exact ⟨replace_maxVLtSome hA lt, replace_maxVLtNone hB⟩ -/
/-   | .abs ty body => by -/
/-     simp only [replace, Nat.succ_eq_add_one, abs.injEq, true_and] -/
/-     exact replace_maxVLtSome (maxVAppSome h) (Nat.succ_lt_succ lt) -/
/- end -/

/- def β (body repl : Stx) : Stx := (body.replace 0 repl).decAbove 0 -/

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
  · exact h
  · exact h

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

theorem VarFwd (h : RefSet (body.β repl) idx) : RefSet (.app (.abs ty body) repl) idx := by
  rw [RefSet_app]
  exact VarFwd_generalized h
