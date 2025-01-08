import Mathlib.Logic.Basic
import LeanScratch.LogicProof.PropLogic.Formula

namespace PLogic

inductive Formula.Dense (Atom : Type)
  | atom (v : Atom)
  | negAtom (v : Atom)

  | conj : Dense Atom → Dense Atom → Dense Atom
  | disj : Dense Atom → Dense Atom → Dense Atom
deriving Repr

def Formula.Dense.toString [ToString Atom] : (Formula.Dense Atom) → String
    | .atom v => s!"{v}"
    | .negAtom v => s!"¬{v}"
    | .conj a b => s!"({a.toString}) ∧ ({b.toString})"
    | .disj a b => s!"({a.toString}) ∧ ({b.toString})"

instance [ToString Atom] : ToString (Formula.Dense Atom) := ⟨Formula.Dense.toString⟩

def Formula.Dense.denote (base : Atom → Prop) : Dense Atom → Prop
  | .atom a    =>  base a
  | .negAtom a => ¬base a
  | .conj a b  => a.denote base ∧ b.denote base
  | .disj a b  => a.denote base ∨ b.denote base

/- #check imp_iff_not_or  -/

def Formula.transform [inst : Inhabited Atom] : Bool → Formula Atom → Dense Atom
  | .false, .f | .true, .t => .disj (.atom inst.default) $ .negAtom inst.default
  | .true, .f | .false, .t => .conj (.atom inst.default) $ .negAtom inst.default
  | .true,  .atom v   => .atom v
  | .false, .atom v   => .negAtom v
  | .true,  .conj a b => .conj (a.transform .true)  (b.transform .true)
  | .false, .conj a b => .disj (a.transform .false) (b.transform .false)
  | .true,  .disj a b => .disj (a.transform .true)  (b.transform .true)
  | .false, .disj a b => .conj (a.transform .false) (b.transform .false)
  | .true,  .imp a b  => .disj (b.transform .true)  (a.transform .false)
  | .false, .imp a b  => .conj (b.transform .false) (a.transform .true)
  | .true,  .iff a b  => .disj (.conj (a.transform .true)  (b.transform .true))
                               (.conj (a.transform .false) (b.transform .false))
  | .false, .iff a b  => .conj (.disj (a.transform .false) (b.transform .false))
                               (.disj (a.transform .true)  (b.transform .true))
  | .true, .neg v     => v.transform .false
  | .false, .neg v    => v.transform .true

mutual
theorem Formula.transform.tCorrect
    (form : Formula Atom) [inst : Inhabited Atom]
    :  form.denote base = (form.transform .true).denote base :=
  match form with
  | .f | .t => by by_cases h : base default
    <;> simp_all only [denote, Dense.denote, not_true_eq_false, and_false, not_false_eq_true, and_true, or_false, or_true]
  | .atom v => by simp only [denote, Dense.denote]
  | .conj a b => by
    simp only [denote, Dense.denote]
    rw [tCorrect a, tCorrect b]
  | .disj a b => by
    simp only [denote, Dense.denote]
    rw [tCorrect a, tCorrect b]
  | .imp a b => by
    simp only [denote, Dense.denote, imp_iff_or_not]
    rw [fCorrect a, tCorrect b]
  | .iff  a b => by
    simp only [denote, iff_iff_and_or_not_and_not (a := denote base a), Dense.denote, eq_iff_iff]
    rw [fCorrect a, fCorrect b, tCorrect a, tCorrect b]
  | .neg v => by
    simp only [denote, Dense.denote, transform]
    rw [fCorrect v]

theorem Formula.transform.fCorrect
    (form : Formula Atom) [inst : Inhabited Atom]
    : (¬form.denote base) = (form.transform .false).denote base :=
  match form with
  | .t | .f => by by_cases h : base default
    <;> simp_all only [denote, not_true_eq_false, Dense.denote, not_false_eq_true, and_true, and_false, or_false, or_true]
  | .atom v => by simp only [denote, Dense.denote]
  | .conj a b => by simp only [Dense.denote, denote, not_and_or, fCorrect a, fCorrect b]
  | .disj a b => by simp only [Dense.denote, denote, not_or, fCorrect a, fCorrect b]
  | .imp  a b => by simp only [denote, Dense.denote, imp_iff_or_not, not_or, not_not, fCorrect b, tCorrect a]
  | .iff  a b => by
    simp only [denote, iff_iff_and_or_not_and_not (a := denote base a), not_and_or, not_or, Dense.denote, not_not]
    rw [fCorrect a, fCorrect b, tCorrect a, tCorrect b]
  | .neg v => by simp only [denote, Dense.denote, not_not, transform, tCorrect v]
end
