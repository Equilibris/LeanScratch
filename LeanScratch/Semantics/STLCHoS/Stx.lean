import Mathlib.Data.Rel
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith.Frontend

namespace STLC

inductive Ty
  | direct (id : ℕ)
  | arr (fn arg : Ty)

def Ty.denote : Ty → Type
  | direct id  => Fin id.succ
  | arr fn arg => fn.denote → arg.denote

infixr:30 " ⇒ " => Ty.arr

inductive Stx' (rep : Ty → Type) : Ty → Type
  | var : rep ty
        → Stx' rep ty
  | abs : (rep iTy → Stx' rep oTy)
        → Stx' rep (iTy ⇒ oTy)
  | app : Stx' rep (iTy ⇒ oTy) → Stx' rep iTy
        → Stx' rep (oTy)
  | fvar : (ty : Ty) → Stx' rep ty

prefix:30 "v:" => Stx'.var
prefix:30 "f:" => Stx'.fvar
prefix:30 "λ:" => Stx'.abs
infixl:30 ";" => Stx'.app

def Stx'.flatten : Stx' (Stx' rep) ty → Stx' rep ty
  | .var v => v
  | .app a b => a.flatten;b.flatten
  | .abs lam => λ: fun x => (lam (.var x)).flatten
  | .fvar v => .fvar v

def Stx (ty : Ty) := {rep : Ty → Type} → Stx' rep ty

def Stx.true  (t1 t2 : Ty) : Stx (t1 ⇒ t2 ⇒ t1) := λ:fun x => λ: fun _ => v: x
def Stx.false (t1 t2 : Ty) : Stx (t1 ⇒ t2 ⇒ t2) := λ:fun _ => λ: fun x => v: x

def Ty.instantiate : (x : Ty) → x.denote
  | .direct x => by
    dsimp [Ty.denote]
    exact 0
  | .arr a b => fun _ => b.instantiate

def Stx'.denote : Stx' Ty.denote ty → ty.denote
  | .var v => v
  | .app a b => a.denote b.denote
  | .abs lam => fun x => (lam x).denote
  | .fvar x => x.instantiate

example := (Stx.true (.direct 1) (.direct 2)).denote

/- def Stx.bvarShift (shift skip : ℕ) : Stx → Stx -/
/-   | .bvar n => .bvar $ if n < skip then n else n + shift -/
/-   | .app a b => .app (a.bvarShift shift skip) (b.bvarShift shift skip) -/
/-   | .abs ty body => .abs ty (body.bvarShift shift skip.succ) -/
/-   | .fvar ty => .fvar ty -/

/- -- Replace also needs to add idx to every value within replace to ensure that the binders still point towards the right points -/
/- def Stx.replace (idx shift : ℕ) (body replace : Stx) : Stx := match body with -/
/-   | .bvar n => if idx = n then replace.bvarShift shift 0 else .bvar n -/
/-   | .app fn arg => .app (fn.replace idx shift replace) (arg.replace idx shift replace) -/
/-   | .abs ty v => .abs ty (v.replace idx.succ shift.succ replace) -/
/-   | .fvar v => .fvar v -/

/- end STLC -/
