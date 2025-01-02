namespace PLogic

inductive Formula (Atom : Type)
  | t | f

  | atom : Atom → Formula Atom
  | conj : Formula Atom → Formula Atom → Formula Atom
  | disj : Formula Atom → Formula Atom → Formula Atom
  | imp  : Formula Atom → Formula Atom → Formula Atom
  | iff  : Formula Atom → Formula Atom → Formula Atom
  | neg  : Formula Atom → Formula Atom

def Formula.denote (base : Atom → Prop) : Formula Atom → Prop
  | .t => True
  | .f => False
  | .atom a => base a
  | .conj a b => a.denote base ∧ b.denote base
  | .disj a b => a.denote base ∨ b.denote base
  | .neg v => ¬v.denote base
  | .iff a b => a.denote base ↔ b.denote base
  | .imp a b => a.denote base → b.denote base

