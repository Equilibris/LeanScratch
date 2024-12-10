import Mathlib.Data.Rel

namespace L1Par

inductive Op
  | add
  | gte

inductive TExpr
  | bool (val : Bool)
  | int  (val : Int)

  | op (lhs : TExpr) (op : Op) (rhs : TExpr)

  | eif    (cond t f : TExpr)
  | ewhile (cond e   : TExpr)

  | assign (addr : String) (e : TExpr)
  | deref (addr : String)
  | seq   (a b : TExpr)
  | skip

  | lock   (name : String)
  | unlock (name : String)

inductive Expr
  | tex (v : TExpr)
  | par (a b : Expr)

inductive TExpr.IsValue : TExpr → Prop
  | bool : IsValue (.bool b)
  | int  : IsValue (.int i)
  | skip : IsValue .skip

inductive Expr.IsValue : Expr → Prop
  | tex : v.IsValue → IsValue (.tex v)
  | par (ha : IsValue a) (hb : IsValue b) : IsValue (.par a b)

