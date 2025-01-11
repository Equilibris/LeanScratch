import Mathlib.Logic.Basic

namespace PLogic
section

variable {α : Type} [DecidableEq α]

def fup (base : α → Prop) (ls : List (α × Bool)) (x : α) : Prop :=
  match ls with
  | [] => base x
  | ⟨hd, .true⟩  :: tl => if x = hd then False else fup base tl x
  | ⟨hd, .false⟩ :: tl => if x = hd then True  else fup base tl x

theorem fup.assoc {base : α → Prop} : fup (fup base l1) l2 = fup base (l2 ++ l1) :=
  match l2 with
  | [] => rfl
  | ⟨hd, .false⟩ :: tl
  | ⟨hd, .true⟩ :: tl => by
    ext x
    by_cases h : x = hd
    <;> simp only [fup, h, ↓reduceIte, List.append_eq]
    exact iff_eq_eq.mpr $ Function.funext_iff.mp fup.assoc x

theorem fup.simpl
    {base : α → Prop} (_ : if b then ¬base v else base v)
    : fup base [⟨v, b⟩] = base := match b with
  | .true | .false => by
    ext x
    dsimp [fup]
    split <;> simp_all only [Bool.false_eq_true, ite_false, ite_true]

theorem fup.either (f : (α → Prop) → Prop) (h : f base) v
    : f (fup base [⟨v, .true⟩]) ∨ f (fup base [⟨v, .false⟩]) := by
  by_cases hBase : base v
  · rw [fup.simpl (b := .false) hBase]
    exact .inr h
  · rw [fup.simpl (b := .true) hBase]
    exact .inl h

def fup.dec
    {base : α → Prop}
    ls
    (h : Decidable (base x)) : Decidable (fup base ls x) :=
  match ls with
  | [] => h
  | ⟨hd, .true⟩ :: tl =>
    if hEq : x = hd then
      .isFalse (by simp only [hEq, fup, ↓reduceIte, not_false_eq_true])
    else
      match fup.dec tl h with
      | .isTrue p => .isTrue (by simp only [fup, hEq, ↓reduceIte, p])
      | .isFalse p => .isFalse (by simp only [fup, hEq, ↓reduceIte, p, not_false_eq_true])
  | ⟨hd, .false⟩ :: tl => 
    if hEq : x = hd then
      .isTrue (by simp only [hEq, fup, ↓reduceIte, not_false_eq_true])
    else
      match fup.dec tl h with
      | .isTrue p => .isTrue (by simp only [fup, hEq, ↓reduceIte, p])
      | .isFalse p => .isFalse (by simp only [fup, hEq, ↓reduceIte, p, not_false_eq_true])
end
