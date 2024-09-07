import Mathlib.Data.Rel
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith.Frontend

namespace L2

inductive Ty
  | bool
  | int
  | void
  | arrow (arg res : Ty)
deriving DecidableEq

inductive Op
  | add
  | gte
deriving DecidableEq

inductive Expr
  | bool (val : Bool)
  | int  (val : Int)
  | skip

  | op (lhs : Expr) (op : Op) (rhs : Expr)

  | eif    (cond t f : Expr)
  | ewhile (cond e   : Expr)

  | assign (addr : String) (e : Expr)
  | deref  (addr : String)

  | seq (a b : Expr)

  | ref (name : String)
  | abs (name : String) (ty : Ty) (body : Expr)
  | app (fn arg : Expr) ---------> inference is decidable this is not needed
                        -- FUN!: Implement unification and make this nicer
inductive BIdxExpr
  | bool (val : Bool)
  | int  (val : Int)
  | skip

  | op (lhs : BIdxExpr) (op : Op) (rhs : BIdxExpr)

  | eif    (cond t f : BIdxExpr)
  | ewhile (cond e   : BIdxExpr)

  | assign (addr : String) (e : BIdxExpr)
  | deref  (addr : String)

  | seq (a b : BIdxExpr)

  | ref (idx : ℕ)
  | abs (ty : Ty) (body : BIdxExpr)
  | app (fn arg : BIdxExpr)

abbrev Expr.toB (ls : List String) : Expr → Option BIdxExpr
  | bool v => return .bool v
  | int  v => return .int  v
  | skip   => return .skip

  | op lhs o rhs => return .op (←lhs.toB ls) o (←rhs.toB ls)

  | eif c t f => return .eif (←c.toB ls) (←t.toB ls) (←f.toB ls)
  | ewhile c body => return .ewhile (←c.toB ls) (←body.toB ls)

  | assign addr e => return .assign addr (←e.toB ls)
  | deref addr    => return .deref addr

  | seq a b => return .seq (←a.toB ls) (←b.toB ls)
  | ref name => return .ref (←ls.indexOf? name)

  | app a b => return .app (←a.toB ls) (←b.toB ls)
  | abs name ty body => return .abs ty (←body.toB (name :: ls))

def BIdxExpr.replace (idx : ℕ) (target replace : BIdxExpr) : BIdxExpr := match target with
  | .bool v => .bool v | .int v => .int v | .skip => .skip
  | .op lhs o rhs => .op (lhs.replace idx replace) o (rhs.replace idx replace)
  | .eif c t f => .eif (c.replace idx replace) (t.replace idx replace) (f.replace idx replace)
  | .ewhile c body => .ewhile (c.replace idx replace) (c.replace idx body)
  | .assign addr e => .assign addr (e.replace idx replace)
  | .deref addr => .deref addr
  | .seq a b => .seq (a.replace idx replace) (b.replace idx replace)
  | .ref jdx => if idx = jdx then replace else .ref jdx
  | .app a b => .app (a.replace idx replace) (b.replace idx replace)
  | .abs ty body => .abs ty (body.replace idx.succ replace)

abbrev BIdxExpr.isInt : BIdxExpr → Prop
  | .int _ => True
  | _ => False
abbrev BIdxExpr.isFnValue : BIdxExpr → Prop
  | .bool _ | .int _ | .skip | .abs _ _ => True
  | _ => False

end L2

