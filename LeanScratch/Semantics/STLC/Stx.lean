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
  | fvar (ty : Ty)
  | app  (fn arg : Stx)
  | abs  (ty : Ty) (body : Stx)

/- scoped prefix:30 "λ: " => Stx.abs -/
/- scoped prefix:30 "b:" => Stx.bvar -/
/- scoped prefix:30 "f:" => Stx.fvar -/
/- scoped infixl:30 " @ " => Stx.app -/

namespace Stx

def bvarShift (shift skip : ℕ) : Stx → Stx
  | .bvar n => .bvar $ if n < skip then n else n + shift
  | .app a b => .app (a.bvarShift shift skip) (b.bvarShift shift skip)
  | .abs ty body => .abs ty (body.bvarShift shift skip.succ)
  | .fvar ty => .fvar ty
def bvarUnShift (shift skip : ℕ) : Stx → Stx
  | .bvar n => .bvar $ if n - shift < skip then n else n - shift
  | .app a b => .app (a.bvarUnShift shift skip) (b.bvarUnShift shift skip)
  | .abs ty body => .abs ty (body.bvarUnShift shift skip.succ)
  | .fvar ty => .fvar ty

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
  <;> dsimp [Stx.bvarShift]
  · split <;> rfl
  case app fn_ih arg_ih =>
    simp only [Stx.app.injEq]
    exact ⟨fn_ih, arg_ih⟩
  case abs ty body ih=>
    simp only [Stx.abs.injEq, true_and]
    exact ih

def maxV : Stx → Option ℕ
  | .bvar n => .some n
  | .fvar _ => .none
  | .abs _ b => b.maxV >>= Nat.ppred
  | .app a b => match a.maxV, b.maxV with
    | .some a, .some b => .some $ max a b
    | .none, .some a | .some a, .none => .some a
    | .none, .none => .none     -- This can be less patterns but this simplifies simps

def minV : Stx → Option ℕ
  | .bvar n => .some n
  | .fvar _ => .none
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
  case fvar ty => simp_all only [minV, Option.bind_eq_bind, Option.none_bind, or_false]
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
    simp [pEqSome] at h
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
  case fvar ty => simp_all only [maxV, Option.bind_eq_bind, Option.none_bind, or_false]
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
    simp [pEqSome] at h
    obtain ⟨w', p'⟩ := Nat.exists_eq_succ_of_ne_zero nez
    rw [p'] at h
    specialize h w' (by simp only [Nat.succ_eq_add_one])
    simp_all only [Nat.succ_eq_add_one, zero_add, Option.bind_eq_bind, Option.some_bind,
      Nat.ppred_succ, Option.some.injEq, one_ne_zero, or_true, false_implies, not_true_eq_false]
theorem maxVAppSome (h : (abs ty body).maxV = some m) : body.maxV = some m.succ := by
  simp [maxV] at h
  by_cases hz : ∃ w, body.maxV = some w
  · rcases hz with ⟨w, p⟩
    simp_all only [Option.some_bind, Nat.ppred_eq_some, Nat.succ_eq_add_one]
  · simp only [not_exists] at hz
    rw [Option.eq_none_iff_forall_not_mem.mpr hz] at h
    contradiction

mutual
theorem bvarShiftNone shift skip (h : body.maxV = none) : (bvarShift shift skip body) = body :=
  match body with
  | .fvar ty => by simp only [bvarShift]
  | .bvar idx => by simp only [bvarShift, maxV] at *
  | .app a b => by
    simp_all only [bvarShift, maxV]
    split at h <;> simp_all
    next ha hb =>
    exact ⟨bvarShiftNone shift skip ha, bvarShiftNone shift skip hb⟩
  | .abs ty body => 
    match maxVEitherZOrNone h with
    | .inl a => by
      simp only [bvarShift, Nat.succ_eq_add_one, abs.injEq, true_and]
      exact bvarShiftNone shift (skip + 1) a
    | .inr a => by
      simp only [bvarShift, Nat.succ_eq_add_one, abs.injEq, true_and]
      exact bvarShiftSkip shift (skip + 1) a (Nat.zero_lt_succ skip)

theorem bvarShiftSkip shift skip (h : body.maxV = some m) (h' : m < skip): (bvarShift shift skip body) = body :=
  match body with
  | .fvar ty => by simp only [bvarShift]
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
        bvarShiftSkip shift skip hFn  ha,
        bvarShiftSkip shift skip hArg hb
      ⟩
    next a hFn hArg =>
      rw [←h] at h'
      exact ⟨
        bvarShiftNone shift skip hFn,
        bvarShiftSkip shift skip hArg h'
      ⟩
    next a hFn hArg =>
      rw [←h] at h'
      exact ⟨
        bvarShiftSkip shift skip hFn h',
        bvarShiftNone shift skip hArg
      ⟩
  | .abs ty body => by
    simp only [bvarShift, Nat.succ_eq_add_one, abs.injEq, true_and]
    exact bvarShiftSkip shift (skip + 1) (maxVAppSome h) (Nat.succ_lt_succ h')
end

/-- info: 'STLC.Stx.bvarShiftSkip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bvarShiftSkip
/-- info: 'STLC.Stx.bvarShiftNone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bvarShiftNone

theorem empty_bvarShift (hMin : s.minV = .none) (hMax : s.maxV = .none) : (bvarShift shift n s).minV = .none ∧ (bvarShift shift n s).maxV = .none :=
  match s with
  | .bvar id => by contradiction
  | .fvar _  => by simp only [minV, maxV, and_self]
  | .abs ty body | .app a b => by
    simp [bvarShiftNone shift n hMax]
    exact ⟨hMin, hMax⟩

def refSet (n : ℕ) : Stx → Set ℕ
  | .bvar id => if id < n then {} else {id - n}
  | .abs _ body => refSet n.succ body
  | .fvar _ => {}
  | .app a b => refSet n a ∪ refSet n b

example : refSet 0 (.abs (.direct 0) (.bvar 0)) = { }                := by simp [refSet]
example : refSet 0 (.abs (.direct 0) (.bvar 1)) = {0}                := by simp [refSet]
example : refSet 0 (bvarShift k n $ .abs (.direct 0) (.bvar 0)) = {} := by simp [refSet]
example : refSet 0 (bvarShift k 0 $ .bvar n) = {n + k}               := by simp [refSet]

example (_ : n < skip) : refSet 0 (bvarShift k skip $ .bvar n) = {n}     := by simp_all [refSet]
example (_ : skip ≤ n) : refSet 0 (bvarShift k skip $ .bvar n) = {n + k} := by simp_all [refSet]
example (_ : skip ≤ n) (_ : z < n + k) : refSet z (bvarShift k skip $ .bvar n) = {n + k - z} := by
  simp_all [refSet, bvarShift]
  split
  <;> split
  · omega
  · omega
  · omega
  · simp_all
example (_ : skip ≤ n) (_ : z < n + k) : refSet z (bvarShift k skip $ .abs ty $ .bvar n.succ) = {n + k - z} := by
  simp_all [refSet, bvarShift]
  split
  <;> split
  · omega
  · omega
  · omega
  · simp only [Set.singleton_eq_singleton_iff]
    omega

example : refSet 1 (.abs (.direct 0) $ .bvar 2) = {0} := by simp [refSet]

/- example : refSet 1 (bvarShift 1 r1 $ .abs ty $ .bvar 2) = {2} := by -/
/-   simp [refSet, bvarShift] -/
/-   split -/
/-   <;> split -/
/-   · omega -/
/-   · omega -/
/-   · sorry -/
/-   · sorry -/

/- def replace.bvar (bvarId idx_shift : ℕ) (replace : Stx) : Stx := -/
/-   match compare bvarId idx_shift with -/
/-   | .lt => .bvar bvarId -/
/-   | .eq => replace.bvarShift idx_shift 0 -/
/-   | .gt => .bvar (bvarId - 1) -- Think this is wrong  -/
def replace.bvar (bvarId idx_shift : ℕ) (replace : Stx) : Stx :=
  if idx_shift = bvarId then replace.bvarShift idx_shift 0
  else .bvar bvarId

-- Replace also needs to add idx to every value within replace to ensure that the binders still point towards the right points
def replace (idx_shift : ℕ) (body replace : Stx) : Stx := match body with
  | .bvar n => Stx.replace.bvar n idx_shift replace
  | .app fn arg => .app (fn.replace idx_shift replace) (arg.replace idx_shift replace)
  | .abs ty v => .abs ty (v.replace idx_shift.succ replace)
  | .fvar v => .fvar v

/- def decAbove (n : ℕ) : Stx → Stx  -/

theorem minVDist {a b : Stx} (h : (a.app b).minV = some bot) :
    (a.minV = .none ∨ (∃ am, a.minV = some am ∧ bot ≤ am)) ∧
    (b.minV = .none ∨ (∃ bm, b.minV = some bm ∧ bot ≤ bm)) := by
  simp only [minV] at h
  split at h
  <;> simp only [Option.some.injEq] at h
  next a b ha hb =>
    rcases min_eq_iff.mp h with (⟨_, _⟩|⟨_, _⟩)
    <;> refine ⟨.inr ⟨_, ha, ?_⟩ , .inr ⟨_, hb, ?_⟩⟩
    <;> simp_all only [min_eq_left_iff, le_refl]
  next ha hb =>
    exact ⟨.inl ha, .inr ⟨_, hb, Nat.le_of_eq (Eq.symm h)⟩⟩
  next ha hb =>
    exact ⟨.inr ⟨_, ha, Nat.le_of_eq (Eq.symm h)⟩, .inl hb⟩

mutual
theorem replace_maxVLtNone {body : Stx} (h : body.maxV = none) : body.replace idx repl = body :=
  match body with
  | .bvar n => by simp only [maxV] at h
  | .fvar ty => by simp only [replace]
  | .app a b => by
    simp [maxV, replace] at h ⊢
    split at h <;> try contradiction
    next ha hb =>
    exact ⟨replace_maxVLtNone ha, replace_maxVLtNone hb⟩
  | .abs ty body => by
    simp only [replace, Nat.succ_eq_add_one, abs.injEq, true_and]
    cases maxVEitherZOrNone h
    case inl h =>
      exact replace_maxVLtNone h
    case inr h =>
      exact replace_maxVLtSome h (Nat.zero_lt_succ idx)

theorem replace_maxVLtSome {body : Stx} (h : body.maxV = some mV) (lt : mV < idx) : body.replace idx repl = body :=
  match body with
  | .bvar n => by
    simp only [maxV, Option.some.injEq] at h
    simp only [replace, replace.bvar, ite_eq_right_iff]
    intro idxEqN
    rw [←h,idxEqN] at lt
    exfalso
    exact (lt_self_iff_false n).mp lt
  | .fvar ty => by simp only [replace]
  | .app a b => by
    simp only [replace, app.injEq]
    simp only [maxV] at h
    split at h
    <;> simp only [Option.some.injEq] at h
    next av bv hA hB =>
      obtain ⟨hALe, hBLe⟩ := Nat.max_le.mp (Nat.le_of_eq h)
      exact ⟨
        replace_maxVLtSome hA (Nat.lt_of_le_of_lt hALe lt),
        replace_maxVLtSome hB (Nat.lt_of_le_of_lt hBLe lt)
      ⟩
    next av hA hB =>
      rw [h] at hB
      exact ⟨replace_maxVLtNone hA, replace_maxVLtSome hB lt⟩
    next bv hA hB =>
      rw [h] at hA
      exact ⟨replace_maxVLtSome hA lt, replace_maxVLtNone hB⟩
  | .abs ty body => by
    simp only [replace, Nat.succ_eq_add_one, abs.injEq, true_and]
    exact replace_maxVLtSome (maxVAppSome h) (Nat.succ_lt_succ lt)
end

def β : Stx → Stx → Stx := (·.replace 0 ·)

/- theorem bvarTranslation (_ : v = .bvar 0) : (bvarShift shift 0 v).refSet n = {0} := by -/
/-   simp_all [refSet] -/
/-   split -/
/-   <;> ext x -/
/-   <;> simp_all -/
/-   · intro h -/
/-     sorry -/
/-   · sorry -/

theorem bvarTranslation : (bvarShift shift 0 v).refSet 0 = { x + shift | x ∈ v.refSet n } := by
  induction v
  <;> simp [refSet]
  case bvar id =>
    ext x
    simp
    constructor
    <;> intro h
    · rw [h]
      use id
      sorry
    · rcases h with ⟨a,b,c⟩
      sorry
  · sorry
  · sorry
  /- induction v generalizing skip n -/
  /- <;> simp [bvarShift, refSet] -/
  /- case bvar id => -/
  /-   split -/
  /-   <;> split -/
  /-   · ext a -/
  /-     simp_all only [Set.mem_empty_iff_false, Set.mem_setOf_eq, false_iff, not_exists, not_and, -/
  /-       and_imp, isEmpty_Prop, not_le, IsEmpty.forall_iff, implies_true] -/
  /-   · ext a -/
  /-     simp_all only [not_lt, Set.mem_singleton_iff, true_and, exists_eq_left, -/
  /-       Set.setOf_eq_eq_singleton'] -/
  /-     split -/
  /-     · constructor -/
  /-       <;> intro h -/
  /-       <;> rw [h] -/
  /-     · simp_all -/
  /-       constructor -/
  /-       <;> intro h -/
  /-       <;> simp_all -/
  /-       · sorry -/
  /-       · sorry -/

  /-   · sorry -/
  /-   · sorry -/
  /- · sorry -/
  /- · sorry -/

example : replace n (bvarShift (.succ k) n body) v = body := by
  induction body generalizing n k
  <;> simp [bvarShift, replace, replace.bvar]
  case bvar id =>
    split
    <;> rename_i x heq
    <;> split at heq
    <;> rename_i h
    <;> simp_all [Nat.compare_eq_lt, Nat.compare_eq_gt, Nat.compare_eq_eq]
    · linarith
    · sorry -- contradictable h, heq
    · linarith
    · split
      <;> rename_i hz
      · sorry -- contradictable
      · clear hz
        simp
        sorry
  case app fn_ih arg_ih =>
    exact ⟨fn_ih, arg_ih⟩
  case abs body_ih => exact body_ih

example : replace 0 (bvarShift 1 0 a) b = a := by
  induction a
  · simp [replace, bvarShift, replace.bvar, Nat.compare_eq_gt.mpr _]
  · simp [replace, bvarShift, replace.bvar, Nat.compare_eq_gt.mpr _]
  · sorry
  · simp [replace, bvarShift, replace.bvar, Nat.compare_eq_gt.mpr _]
    sorry


/- theorem β_bvarShift_inverse : (Stx.bvarShift 1 0 z).β v = z := by -/
/-   induction z -/
/-   <;> simp [bvarShift, β, replace, replace.bvar, replace] -/
/-   · sorry -/
/-   · sorry -/
/-   /- <;> simp [bvarShift, β, replace, replace.bvar, replace] -/ -/
/-   /- case app fn_ih arg_ih => -/ -/
/-   /-   sorry -/ -/
/-   /- case abs ty body body_ih => -/ -/
/-   /-   sorry -/ -/

end STLC.Stx
