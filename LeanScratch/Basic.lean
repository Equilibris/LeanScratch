import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Init.Set
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Data.Complex.Basic


section

variable (r : Ring α) [Dvd (Ring α)]

def adjoin (s : Set α) (i : α): Set α := setOf fun (val : α) =>
  ∃ a : α, ∃ base ∈ s, ∃ c : α, val = base * c + i * a

abbrev multipleSet (base : α) := setOf fun (i : α) => base ∣ i

abbrev closedUnder (s : Set α) (other : Set β) (op : α → β → α) : Prop :=
  ∀ a ∈ s, ∀ b ∈ other, op a b ∈ s

class Ideal (s : α → Prop) where
  contains_zero : s r.zero
  closedUnder_add : closedUnder s s r.add
  closedUnder_mul : ∀ p : α → Prop, closedUnder s p r.mul

  s := s

theorem multipleSet_contains_zero (base: α) : r.zero ∈ multipleSet r base := by
  apply dvd_def.mpr
  use 0
  rw [mul_zero]
  rfl

theorem multipleSet_closedUnder_add (base : α) :
  closedUnder (multipleSet r base) (multipleSet r base) r.add := by
  intro a ⟨w_a, h_a⟩
  intro b ⟨w_b, h_b⟩
  simp [multipleSet, *]

  apply dvd_def.mpr
  use w_a + w_b

  rw [mul_add]
  rfl

theorem multipleSet_closedUnder_mul (base : α) (s : Set α) :
  closedUnder (multipleSet r base) s r.mul := by
  intro a ⟨w_a, h_a⟩
  intro b _
  simp [multipleSet, *]

  apply dvd_def.mpr
  use w_a * b

  rw [←mul_assoc]
  rfl

instance (base : α) : Ideal r (multipleSet r base) where
  contains_zero := multipleSet_contains_zero r base
  closedUnder_add := multipleSet_closedUnder_add r base
  closedUnder_mul := multipleSet_closedUnder_mul r base

  s := multipleSet r base

def total (s : Set α) [Ideal r s]: Prop := ∀ a : α, a ∈ s

set_option pp.explicit true in
theorem multipleSet1_total : total r (multipleSet r r.one) := by
  intro a
  apply dvd_def.mpr
  use a
  have : 1 = One.one := by rfl

  /- rw [this, one_mul a] -/
  sorry


end

/- abbrev intComplex (v : Complex) := ∃ a : ℤ, ∃ b : ℤ, a = v.re ∧ b = v.im  -/

/- theorem intComplex_closedUnder_add :  -/

/- def Ic := { v : Complex // intComplex v} -/



/- def Cx.add (a : Cx) (b : Cx): Cx := -/
/-   { re := a.re + b.re, im := a.im + b.im } -/
/- def Cx.mul (a : Cx) (b : Cx): Cx := -/
/-   { re := a.re * b.re - a.im * b.im, im := a.im * b.re + a.re * b.im } -/

/- @[simp] -/
/- theorem add_def (a : Cx) (b : Cx): Cx.add a b =  -/
/-   ({ re := a.re + b.re, im := a.im + b.im } : Cx) := by -/
/-   trivial -/

/- instance : Ring Cx where -/
/-   add := Cx.add -/
/-   mul := Cx.mul -/
  
/-   add_assoc a b c := by -/
/-     rcases a with ⟨are, aim⟩ -/
/-     rcases b with ⟨bre, bim⟩ -/
/-     rcases c with ⟨cre, cim⟩ -/
    

  
  

