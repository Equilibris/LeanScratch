import Mathlib.Tactic.Linarith.Frontend

theorem List.getElem?_lt_length {ls : List α} (h : ls[n]? = some v) : n < ls.length :=
  match ls with
  | .nil => Option.noConfusion h
  | .cons hd tl =>
    match n with
    | 0 => Nat.zero_lt_succ _
    | n+1 => by
      rw [List.length_cons, add_lt_add_iff_right]
      rw [List.getElem?_cons_succ] at h
      exact List.getElem?_lt_length h

theorem List.eraseIdx_pre_k
    {k : Nat} {ls : List α} (shorter : k < n)
    (hv : (ls.eraseIdx n)[k]? = some z) : (ls[k]? = some z) := by
  induction ls, n using List.eraseIdx.induct generalizing k
  <;> dsimp [List.eraseIdx] at hv
  <;> (try contradiction)
  next hd tl n ih =>
    cases k
    · rw [List.getElem?_cons_zero, Option.some.injEq] at hv ⊢
      exact hv
    next n' =>
      rw [List.getElem?_cons_succ] at hv ⊢
      rw [add_lt_add_iff_right] at shorter
      exact ih shorter hv

theorem List.eraseIdx_post_k
    {k : Nat} {ls : List α} (shorter : n ≤ k)
    (hv : (ls.eraseIdx n)[k]? = some z) : (ls[k+1]? = some z) := by
  induction ls, n using List.eraseIdx.induct generalizing k
  <;> dsimp only [List.eraseIdx] at hv
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

theorem List.getLast?_eq_cons (h : tl.getLast? = some v) : (hd :: tl).getLast? = some v := by
  rw [List.getLast?_eq_get?] at h ⊢
  simp_all []
  cases tl
  · contradiction
  · simp_all only [length_cons, add_tsub_cancel_right, lt_add_iff_pos_right, zero_lt_one,
      getElem?_eq_getElem, Option.some.injEq, getElem_cons_succ]

