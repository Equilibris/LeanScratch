import Mathlib.Data.Rel
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith.Frontend

namespace L2

inductive Ty
  | bool
  | int
  | void
  | arrow (arg res : Ty)
deriving DecidableEq, Repr

inductive Op
  | add
  | gte
deriving DecidableEq, Repr

inductive Expr
  | bool (val : Bool)
  | int  (val : Int)
  | skip

  | op (lhs : Expr) (op : Op) (rhs : Expr)

  | eif    (cond t f : Expr)
  | ewhile (cond e   : Expr)

  | assign (addr : String) (e : Expr)
  | deref (addr : String)

  | seq   (a b : Expr)

  | bvar (idx : ℕ)
  | abs (ty : Ty) (body : Expr)
  | app (fn arg : Expr) ---------> inference is decidable this is not needed
                        -- FUN!: Implement unification and make this nicer
deriving DecidableEq, Repr

end L2

