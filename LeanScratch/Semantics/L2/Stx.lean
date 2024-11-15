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
  | letVal (t : Ty) (val body : Expr)
  | letRecVal (t : Ty) (val body : Expr)
deriving DecidableEq, Repr

namespace Expr

inductive IsValue : Expr → Prop
  | bool : IsValue (.bool b)
  | int : IsValue (.int i)
  | skip : IsValue .skip
  | fn : IsValue (.abs ty body)

def bvarShift (shift skip : ℕ) : Expr → Expr
  | .bvar n => .bvar $ if n < skip then n else n + shift
  | .abs ty body => .abs ty (body.bvarShift shift skip.succ)
  | .letVal t val body =>
    .letVal    t (val.bvarShift shift skip     ) (body.bvarShift shift skip.succ)
  | .letRecVal t val body =>
    .letRecVal t (val.bvarShift shift skip.succ) (body.bvarShift shift skip.succ)

  | .app a b => .app (a.bvarShift shift skip) (b.bvarShift shift skip)
  | .seq a b => .seq (a.bvarShift shift skip) (b.bvarShift shift skip)
  | .assign addr body => .assign addr (body.bvarShift shift skip)
  | .ewhile c body => .ewhile (c.bvarShift shift skip) (body.bvarShift shift skip)
  | .eif c t f => .eif (c.bvarShift shift skip) (t.bvarShift shift skip) (f.bvarShift shift skip)
  | .op a o b => .op (a.bvarShift shift skip) o (b.bvarShift shift skip)
  | x@(.deref _)
  | x@(.skip)
  | x@(.int _)
  | x@(.bool _) => x

def replace.bvar (bvarId idx_shift : ℕ) (replace : Expr) : Expr :=
  match compare bvarId idx_shift with
  | .lt => .bvar bvarId
  | .eq => replace.bvarShift idx_shift 0
  | .gt => .bvar bvarId.pred

def replace (idx_shift : ℕ) (body repl : Expr) : Expr := match body with
  | .bvar n => replace.bvar n idx_shift repl
  | .abs ty body => .abs ty (body.replace idx_shift.succ repl)
  | .letVal t val body =>
    .letVal    t (val.replace idx_shift      repl) (body.replace idx_shift.succ repl)
  | .letRecVal t val body =>
    .letRecVal t (val.replace idx_shift.succ repl) (body.replace idx_shift.succ repl)

  | .app a b => .app (a.replace idx_shift repl) (b.replace idx_shift repl)
  | .seq a b => .seq (a.replace idx_shift repl) (b.replace idx_shift repl)
  | .assign addr body => .assign addr (body.replace idx_shift repl)
  | .ewhile c body => .ewhile (c.replace idx_shift repl) (body.replace idx_shift repl)
  | .eif c t f => .eif (c.replace idx_shift repl) (t.replace idx_shift repl) (f.replace idx_shift repl)
  | .op a o b => .op (a.replace idx_shift repl) o (b.replace idx_shift repl)
  | x@(.deref _)
  | x@(.skip)
  | x@(.int _)
  | x@(.bool _) => x

def β : Expr → Expr → Expr := replace 0

