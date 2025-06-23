namespace PMLogic

inductive Formula (Atom : Type)
  | t | f

  | atom : Atom → Formula Atom
  | conj : Formula Atom → Formula Atom → Formula Atom
  | disj : Formula Atom → Formula Atom → Formula Atom
  | imp  : Formula Atom → Formula Atom → Formula Atom
  | iff  : Formula Atom → Formula Atom → Formula Atom
  | neg  : Formula Atom → Formula Atom
  | dia  : Formula Atom → Formula Atom
  | box  : Formula Atom → Formula Atom
deriving Repr

declare_syntax_cat mlog

syntax "[" term "]" : mlog
syntax "(" mlog ")" : mlog
syntax mlog "∧" mlog : mlog
syntax mlog "∨" mlog : mlog
syntax mlog "→" mlog : mlog
syntax mlog "↔" mlog : mlog
syntax "¬" mlog : mlog
syntax "◇" mlog : mlog
syntax "□" mlog : mlog

syntax "[m|" mlog "]" : term

macro_rules
  | `([m| [$t:term] ]) => `(.atom $t)
  | `([m| ($m:mlog) ]) => `([m| $m])
  | `([m| $a ∧ $b ]) => `(.conj [m| $a] [m| $b])
  | `([m| $a ∨ $b ]) => `(.disj [m| $a] [m| $b])
  | `([m| $a → $b ]) => `(.imp [m| $a] [m| $b])
  | `([m| $a ↔ $b ]) => `(.imp [m| $a] [m| $b])
  | `([m| ¬$b:mlog ]) => `(.neg [m| $b])
  | `([m| □$b:mlog ]) => `(.box [m| $b])
  | `([m| ◇$b:mlog ]) => `(.dia [m| $b])

open Lean in
def uex_inner : Syntax.Term → PrettyPrinter.UnexpandM (TSyntax `mlog)
  | `([m|$b:mlog]) => do `(mlog|$b)
  | `($t:term) => do `(mlog|[$t])

@[app_unexpander Formula.atom]
def Formula.atom.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $b) => do `([m| [$b]])
  | _ => throw ()
@[app_unexpander Formula.conj]
def Formula.conj.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $a $b) => do `([m| $(← uex_inner a) ∧ $(← uex_inner b)])
  | _ => throw ()
@[app_unexpander Formula.disj]
def Formula.disj.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $a $b) => do `([m| $(← uex_inner a) ∨ $(← uex_inner b)])
  | _ => throw ()
@[app_unexpander Formula.imp]
def Formula.imp.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $a $b) => do `([m| $(← uex_inner a) → $(← uex_inner b)])
  | _ => throw ()
@[app_unexpander Formula.iff]
def Formula.iff.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $a $b) => do `([m| $(← uex_inner a) ↔ $(← uex_inner b)])
  | _ => throw ()
@[app_unexpander Formula.neg]
def Formula.neg.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $b) => do `([m| ¬$(← uex_inner b):mlog])
  | _ => throw ()
@[app_unexpander Formula.box]
def Formula.box.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $b) => do `([m| □$(← uex_inner b):mlog])
  | _ => throw ()
@[app_unexpander Formula.dia]
def Formula.dia.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $b) => do `([m| ◇$(← uex_inner b):mlog])
  | _ => throw ()

def Formula.denote (w : World) (R : World → World → Prop) (I : Atom → World → Prop) : Formula Atom → Prop
  | .box v => ∀ w', R w w' → v.denote w' R I
  | .dia v => ∃ w', R w w' → v.denote w' R I

  | .t => True
  | .f => False
  | .atom a => I a w
  | .conj a b => a.denote w R I ∧ b.denote w R I
  | .disj a b => a.denote w R I ∨ b.denote w R I
  | .neg v => ¬v.denote w R I
  | .iff a b => a.denote w R I ↔ b.denote w R I
  | .imp a b => a.denote w R I → b.denote w R I

def Formula.sat (R : World → World → Prop) (form : Formula Atom) : Prop := ∃ I, ∀ w, form.denote w R I
def Formula.val (R : World → World → Prop) (form : Formula Atom) : Prop := ∀ I, ∀ w, form.denote w R I

/- class S4 (R : World → World → Prop) where -/


