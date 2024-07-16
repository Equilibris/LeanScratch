import Mathlib.Data.Rel

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

