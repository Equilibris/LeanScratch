import Mathlib.Data.Rel
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith.Frontend

namespace L3

@[aesop safe [constructors, cases]]
inductive Ty
  | bool
  | int
  | void
  | arrow (arg res : Ty)
  | prod (a b : Ty)
  | sum  (a b : Ty)

  | ref (t : Ty)
deriving DecidableEq, Repr

inductive Op
  | add
  | gte
deriving DecidableEq, Repr

@[aesop safe [constructors, cases]]
inductive Expr
  | bool (val : Bool)
  | int  (val : Int)
  | skip

  | op (lhs : Expr) (op : Op) (rhs : Expr)

  | eif    (cond t f : Expr)
  | ewhile (cond e   : Expr)

  | ref (t : Ty) (e : Expr)
  | loc (t : Ty) (l : ℕ)

  | assign (addr : Expr) (e : Expr)
  | deref  (addr : Expr)

  | seq   (a b : Expr)

  | bvar (idx : ℕ)
  | abs (ty : Ty) (body : Expr)
  | app (fn arg : Expr)

  | letVal (t : Ty) (val body : Expr)

  | pair (a b : Expr)
  | fst (body : Expr)
  | snd (body : Expr)

  | inl (other : Ty) (body : Expr)
  | inr (other : Ty) (body : Expr)
  | case (scrutinee a b : Expr)
  -- cant be fucked to deal with these rn
  /- | letRecVal (t : Ty) (val body : Expr) -/
deriving DecidableEq, Repr

namespace Expr

inductive IsValue : Expr → Prop
  | bool : IsValue (.bool b)
  | int : IsValue (.int i)
  | skip : IsValue .skip
  | fn : IsValue (.abs ty body)

  | pair : IsValue a → IsValue b → IsValue (.pair a b)
  | inl : IsValue a → IsValue (.inl _ a)
  | inr : IsValue a → IsValue (.inr _ a)
  | loc : IsValue (.loc _ v)

def bvarShift (shift skip : ℕ) : Expr → Expr
  | .bvar n => .bvar $ if n < skip then n else n + shift
  | .abs ty body => .abs ty (body.bvarShift shift skip.succ)
  | .letVal t val body =>
    .letVal    t (val.bvarShift shift skip     ) (body.bvarShift shift skip.succ)

  | .pair a b => .pair (a.bvarShift shift skip) (b.bvarShift shift skip)
  | .fst body => .fst (body.bvarShift shift skip)
  | .snd body => .fst (body.bvarShift shift skip)

  | .case scrutinee a b => .case (scrutinee.bvarShift shift skip) (a.bvarShift shift skip.succ) (b.bvarShift shift skip.succ)
  | .inl other body => .inl other (body.bvarShift shift skip)
  | .inr other body => .inr other (body.bvarShift shift skip)

  | .app a b => .app (a.bvarShift shift skip) (b.bvarShift shift skip)
  | .seq a b => .seq (a.bvarShift shift skip) (b.bvarShift shift skip)
  | .assign addr body => .assign (addr.bvarShift shift skip) (body.bvarShift shift skip)
  | .deref body       => .deref (body.bvarShift shift skip)
  | .ewhile c body => .ewhile (c.bvarShift shift skip) (body.bvarShift shift skip)
  | .eif c t f => .eif (c.bvarShift shift skip) (t.bvarShift shift skip) (f.bvarShift shift skip)
  | .op a o b => .op (a.bvarShift shift skip) o (b.bvarShift shift skip)

  | x@(.ref _ _) | x@(.loc _ _) | x@(.skip) | x@(.int _) | x@(.bool _) => x

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

  | .pair a b => .pair (a.replace idx_shift repl) (b.replace idx_shift repl)
  | .fst body => .fst (body.replace idx_shift repl)
  | .snd body => .fst (body.replace idx_shift repl)

  | .case scrutinee a b => .case (scrutinee.replace idx_shift repl) (a.replace idx_shift.succ repl) (b.replace idx_shift.succ repl)
  | .inl other body => .inl other (body.replace idx_shift repl)
  | .inr other body => .inr other (body.replace idx_shift repl)

  | .app a b => .app (a.replace idx_shift repl) (b.replace idx_shift repl)
  | .seq a b => .seq (a.replace idx_shift repl) (b.replace idx_shift repl)
  | .assign addr body => .assign (addr.replace idx_shift repl) (body.replace idx_shift repl)
  | .deref body       => .deref (body.replace idx_shift repl)
  | .ewhile c body => .ewhile (c.replace idx_shift repl) (body.replace idx_shift repl)
  | .eif c t f => .eif (c.replace idx_shift repl) (t.replace idx_shift repl) (f.replace idx_shift repl)
  | .op a o b => .op (a.replace idx_shift repl) o (b.replace idx_shift repl)

  | x@(.ref _ _) | x@(.loc _ _)  | x@(.skip) | x@(.int _) | x@(.bool _) => x

def β : Expr → Expr → Expr := replace 0

