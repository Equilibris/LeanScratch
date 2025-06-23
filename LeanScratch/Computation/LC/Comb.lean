import LeanScratch.Computation.LC.Stx
import LeanScratch.Computation.LC.Beta
import LeanScratch.Computation.LC.Red

namespace LC

namespace Stx

def I : Stx := [l|λx. x]
def K : Stx := [l|λx y. x]
def S : Stx := [l|λx y z. (x z) (y z)]
def U : Stx := [l|λx. x x]
def Θ : Stx := [l|(λ x y. y ((x x) y)) (λ x y. y ((x x) y))]

theorem I.unfold : [l|I x] →ᵣ x := by
  nth_rw 2 [←shift0 (body := x)]
  exact .beta

theorem K.unfold : [l|(K x) y] →ᵣ* x := calc
  _ →ᵣ* _ := by exact .single $ .appl $ .beta
  _ →ᵣ* _ := by exact .single .beta
  _ →ᵣ* _ := by
    simp only [Nat.succ_eq_add_one, Nat.zero_add, replace_bvar, shift_replace]
    exact .refl

theorem S.unfold : [l|((S x) y) z] →ᵣ* [l|(x z) (y z)] := calc
  _ →ᵣ* _ := by exact .single $ .appl $ .appl $ .beta
  _ →ᵣ* _ := by exact .single $ .appl $ .beta
  _ →ᵣ* _ := by exact .single $ .beta
  _ →ᵣ* _ := by
    simp only [Nat.succ_eq_add_one, Nat.zero_add, Nat.reduceAdd, replace_app, replace_bvar,
      Nat.zero_lt_succ, replace_bvar_gt, Nat.lt_succ_self, Nat.zero_le, le_refl, shift_replace',
      shift0]
    exact .refl

theorem U.unfold : [l|U x] →ᵣ [l|x x] := by
  have h : [l| x x] = [l|0 0].replace 0 x := by simp
  rw [h]
  exact .beta

theorem Θ.unfold : [l| Θ x] →ᵣ* [l| x (Θ x)] := calc
  /- _ →ᵣ* _ := by exact .tail .refl $ .appl U.unfold -/
  _ →ᵣ* _ := by exact .single $ .appl .beta
  _ →ᵣ* _ := by exact .single $ .beta
  _ →ᵣ* _ := by
    simp only [Nat.succ_eq_add_one, Nat.zero_add, replace_app, Nat.lt_succ_self, replace_bvar_gt,
      replace_bvar, shift, Nat.reduceAdd, Nat.zero_lt_succ, ↓reduceIte, shift0, replace_abs]
    exact .refl

