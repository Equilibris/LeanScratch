import LeanScratch.Vec
import LeanScratch.LogicProof.FirstOrderLogic.Formula


namespace FOL.DeBrujin

inductive Dense.Base {TNm PNm : Type} (TA : TNm → Nat) (PA : PNm → Nat) (n : Nat)
  | pred  (nm : PNm) (app : Vec (Term TA n) (PA nm)) : Base TA PA n
  | npred (nm : PNm) (app : Vec (Term TA n) (PA nm)) : Base TA PA n

  | conj : Base TA PA n → Base TA PA n → Base TA PA n
  | disj : Base TA PA n → Base TA PA n → Base TA PA n

def Dense.Base.bvarShift (k : Nat) : Base TA PA n → Base TA PA (n + k)
  | .pred nm app => .pred nm $ Term.bvarShift.mapper _ app
  | .npred nm app => .pred nm $ Term.bvarShift.mapper _ app
  | .disj a b => .disj (a.bvarShift k) (b.bvarShift k)
  | .conj a b => .conj (a.bvarShift k) (b.bvarShift k)

inductive Dense {TNm PNm : Type} (TA : TNm → Nat) (PA : PNm → Nat) : Nat → Type
  | bot : Dense.Base TA PA n → Dense TA PA n
  | exis : Dense TA PA n.succ → Dense TA PA n
  | univ : Dense TA PA n.succ → Dense TA PA n

/- def Dense.conjunctiveTransform : Dense TA PA n → Dense TA PA (n + k) → Dense TA PA (n + k) -/
/-   | .bot x, .bot y  => .bot (.conj (x.bvarShift k) y) -/
/-   | x, .univ y => .univ (conjunctiveTransform (k := k + 1) x y) -/
/-   | x, .exis y => .exis (conjunctiveTransform (k := k + 1) x y) -/
/-   | .exis x, y => match k with -/
/-     | 0 => .exis $ conjunctiveTransform (n := n) (k := 1) y x -/
/-     | k+1 => -/
/-       /- have : Dense TA PA := sorry -/ -/
/-       .exis sorry -/
/-   | .univ x, y => sorry -/
  /- | .univ x, .univ y => .univ $ conjunctiveTransform x y -/
  /- | y, .univ x | .univ x, y => .univ fun v => conjunctiveTransform (x v) y -/
  /- | y, .exis x | .exis x, y => .exis fun v => conjunctiveTransform (x v) y -/

-- Since n represents free varaibles this will always be the same but the way
-- these are bound by quiantifiers will strictly vary due to how PNX NF works
def Formula.transform : Bool → Formula TA PA n → Dense TA PA n
  | .true, .pred nm app  => .bot $ .pred nm app
  | .false, .pred nm app => .bot $ .npred nm app

  | .true,  .conj a b => sorry-- conjunctiveTransform (a.transform .true) (b.transform .true)
  | .false, .conj a b => sorry
  | .true,  .disj a b => sorry
  | .false, .disj a b => sorry
  | .true,  .imp a b  => sorry
  | .false, .imp a b  => sorry
  | .true,  .iff a b  => sorry
  | .false, .iff a b  => sorry
  | .true,  .neg v    => v.transform .false
  | .false, .neg v    => v.transform .true

  | .true,  .exis v => .exis $ v.transform .true
  | .true,  .univ v => .univ $ v.transform .true
  | .false, .exis v => .univ $ v.transform .false
  | .false, .univ v => .exis $ v.transform .false

example {P R : α → Prop} : (∀ x, P x) ∧ (∀ x, R x) ↔ ∀ x, P x ∧ R x := by
  exact Iff.symm forall_and
