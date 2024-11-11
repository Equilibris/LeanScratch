import Mathlib.Data.Rel
/- import Mathlib.Tactic.Linarith -/

inductive Ex1 (p : α → Prop) : Prop
  | intro (a : α) : p a → Ex1 p

inductive Fa1 (p : α → Prop) : Prop
  | intro (a : α → p a)

inductive Even : ℕ → Prop
  | zero : Even 0
  | twoSucc : Even n → Even (n + 2)

inductive Odd : ℕ → Prop
  | one : Odd 1
  | twoSucc : Odd n → Odd (n + 2)

theorem Even_iff_not_succ_Even : Even n ↔ ¬Even n.succ := by
  constructor
  · intro h v
    induction n
    · cases v
    case succ ih =>
      cases v; next v =>
      exact ih v h
  · intro h
    induction n
    · exact .zero
    next ih =>
      by_contra!
      exact h (.twoSucc $ ih this)

theorem Odd_iff_not_succ_Odd : ¬Odd n ↔ Odd n.succ := by
  constructor
  · intro h
    induction n
    · exact .one
    next ih =>
      refine .twoSucc ?_
      by_contra!
      exact h $ ih this
  · intro hS h
    induction n
    · cases h
    next ih =>
      cases hS; next hS =>
      exact ih h hS

lemma Odd_notEven (h : Odd n) : ¬Even n := by
  induction h
  · intro h
    cases h
  next _ ih =>
    intro h
    cases h
    trivial

lemma Even_notOdd (h : Even n) : ¬Odd n := by
  induction h
  · intro h
    cases h
  next _ ih =>
    intro h
    cases h
    trivial

theorem Odd_iff_not_Even : Odd n ↔ ¬ Even n := by
  constructor
  <;> intro h
  · exact Odd_notEven h
  · cases n
    · exfalso
      exact h .zero
    next n =>
      rw [Even_iff_not_succ_Even, not_not] at h
      rcases h with (h|h)
      by_contra!
      rw [Odd_iff_not_succ_Odd] at this
      rcases this with (a|a)
      exact Even_notOdd h a

theorem Even_iff_exN : Even a ↔ ∃ n, n + n = a := by
  constructor
  · intro h
    induction h
    · use 0
    next n _ ih =>
      rcases ih with ⟨w, p⟩
      use (w+1)
      calc
        w + 1 + w + 1   = _ := by rw [Nat.add_comm (w + 1), ←Nat.add_assoc]
        w + w + 1 + 1   = _ := by rw [p]
  · rintro ⟨w, p⟩
    rw [←p]
    clear p
    induction w
    · exact .zero
    next w ih =>
      rw [←Nat.add_assoc, ←Nat.add_comm w, ←Nat.add_assoc]
      exact .twoSucc ih


theorem Odd_iff_exN : Odd a ↔ ∃ n, n + n + 1 = a := by
  constructor
  · intro h
    induction h
    · use 0
    next n _ ih =>
      rcases ih with ⟨w, p⟩
      use (w+1)
      rw [←Nat.add_assoc, ←Nat.add_comm w, ←Nat.add_assoc, p]
  · rintro ⟨w, p⟩
    rw [←p]
    clear p
    induction w
    · exact .one
    next w ih =>
      rw [←Nat.add_assoc, ←Nat.add_comm w, ←Nat.add_assoc]
      exact .twoSucc ih

example (ha : Odd a) (hb : Odd b) : Even (a + b) := by
  rw [Odd_iff_exN] at ha hb
  rcases ha with ⟨wa, rfl⟩
  rcases hb with ⟨wb, rfl⟩
  rw [Even_iff_exN]
  use wa + wb + 1

  omega

