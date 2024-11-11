import LeanScratch.Semantics.STLC.Stx

namespace STLC.Stx

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

lemma RefSet_dist : RefSet (.abs ty (.app a b)) idx ↔ RefSet (.abs ty a) idx ∨ RefSet (.abs ty b) idx := by
  constructor
  <;> intro h
  <;> simp only [RefSet_abs, RefSet_app] at h ⊢
  <;> exact h

