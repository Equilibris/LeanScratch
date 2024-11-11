import Mathlib.Data.Rel

namespace L1

inductive Op
  | add
  | gte

inductive Expr
  | bool (val : Bool)
  | int  (val : Int)

  | op (lhs : Expr) (op : Op) (rhs : Expr)

  | eif    (cond t f : Expr)
  | ewhile (cond e   : Expr)

  | assign (addr : String) (e : Expr)
  | deref (addr : String)
  | seq   (a b : Expr)
  | skip

declare_syntax_cat l1

syntax "TRUE" : l1
syntax "FALSE" : l1

syntax num : l1
syntax "-"num : l1

syntax l1 "+" l1 : l1
syntax l1 "≥" l1 : l1

syntax "if" l1 "then" l1 "else" l1 : l1
syntax "while" l1 "do" l1 : l1

syntax ident ":=" l1 : l1
syntax "!" ident : l1
syntax l1 ";" l1 : l1

syntax "SKIP" : l1
syntax "(" l1 ")" : l1
syntax "[l1|" l1 "]" : term

macro_rules
  | `([l1| TRUE]) => `(Expr.bool .true)
  | `([l1| FALSE]) => `(Expr.bool .false)
  | `([l1| SKIP]) => `(Expr.skip)

  | `([l1| $i:num]) => `(Expr.int $i)
  | `([l1| -$i:num]) => `(Expr.int (-($i : Int)))

  | `([l1| $a:l1 + $b:l1]) => `(Expr.op [l1|$a] .add [l1|$b])
  | `([l1| $a:l1 ≥ $b:l1]) => `(Expr.op [l1|$a] .gte [l1|$b])
  | `([l1| if $c:l1 then $a:l1 else $b:l1]) => `(Expr.eif [l1|$c] [l1|$a] [l1|$b])
  | `([l1| while $c:l1 do $a:l1]) => `(Expr.ewhile [l1|$c] [l1|$a])

  | `([l1| $nm:ident := $body:l1]) => `(Expr.assign $(⟨Lean.Syntax.mkStrLit nm.getId.toString⟩) [l1|$body])
  | `([l1| !$nm:ident]) => `(Expr.deref $(⟨Lean.Syntax.mkStrLit nm.getId.toString⟩))
  | `([l1| $a:l1; $b:l1]) => `(Expr.seq [l1|$a] [l1|$b])
  | `([l1| ($a:l1)]) => `([l1|$a])

def Expr.isInt : Expr → Bool
  | .int _ => true
  | _ => false

theorem isInt_defn {e : Expr} : (∃ i, e = .int i) ↔ e.isInt := by
  constructor
  <;> intro h
  · rcases h with ⟨_, h⟩
    rw [h]
    simp [Expr.isInt]
  · cases e
    <;> simp [Expr.isInt] at h
    case int v =>
      use v

def Expr.isValue: Expr → Bool
  | .bool _ | .int _ | .skip => true
  | _ => false

end L1

