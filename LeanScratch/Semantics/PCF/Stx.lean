import Mathlib.Data.Rel
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith.Frontend
import LeanScratch.Fin2

namespace PCF

inductive Ty
  | bool
  | nat
  | arrow (arg res : Ty)
deriving DecidableEq, Repr

inductive Expr : List Ty → Ty → Type
  | zero : Expr Γ .nat
  | succ (e : Expr Γ .nat) : Expr Γ .nat
  | pred (e : Expr Γ .nat) : Expr Γ .nat

  | tt : Expr Γ .bool
  | ff : Expr Γ .bool
  | z? (e : Expr Γ .nat) : Expr Γ .bool

  | eif (cond : Expr Γ .bool) (t f : Expr Γ τ) : Expr Γ τ

  | bvar idx : Expr Γ (Γ.getFin2 idx)
  | abs (ty : Ty) (body : Expr (ty :: Γ) ret) : Expr Γ (.arrow ty ret)
  | app (fn : Expr Γ (.arrow arg ret)) (arg : Expr Γ arg) : Expr Γ ret
  | fix (e : Expr Γ (.arrow τ τ)) : Expr Γ τ
deriving Repr

namespace Expr

inductive IsValue : Expr Γ τ → Prop
  | tt : IsValue .tt
  | ff : IsValue .ff
  | zero : IsValue .zero
  | succ : IsValue a → IsValue (.succ a)
  | fn : IsValue (.abs ty body)

def extend {c : List α} : {a b : List α} → Fin2 (a ++ c).length → Fin2 (a ++ b ++ c).length
  | [], [], x => x
  | [], _ :: tb, v => .fs $ extend v
  | _ :: ta, b, .fz => .fz
  | _ :: ta, b, .fs v => .fs $ extend v

theorem extend.eq {c : List α}
    : {a b : List α}
    → {i : Fin2 (a ++ c).length}
    → (a ++ c).getFin2 i = (a ++ b ++ c).getFin2 (@extend _ c a b i) := by
  intro a b i
  induction a, b, i using extend.induct
  <;> unfold extend
  any_goals rfl
  all_goals assumption

def bvarShift : Expr (Γskip ++ Γ₁) τ → Expr (Γskip ++ Γshift ++ Γ₁) τ
  | .bvar n =>
    cast (congr rfl extend.eq.symm) $ .bvar (extend n)
  | .abs ty body => .abs ty (body.bvarShift (Γskip := ty :: Γskip))
  | .app a b => .app a.bvarShift b.bvarShift
  | .eif c t f => .eif c.bvarShift t.bvarShift f.bvarShift
  | .succ v => .succ v.bvarShift
  | .pred v => .pred v.bvarShift
  | .fix v => .fix v.bvarShift
  | .z? v => .z? v.bvarShift
  | .tt => .tt
  | .ff => .ff
  | .zero => .zero

def bvarShift' : Expr Γ₁ τ → Expr (Γshift ++ Γ₁) τ := bvarShift (Γskip := [])

/- def replace.bvar (bvarId idx_shift : ℕ) (replace : Expr) : Expr _ τ := -/
/-   match compare bvarId idx_shift with -/
/-   | .lt => .bvar bvarId -/
/-   | .eq => replace.bvarShift idx_shift 0 -/
/-   | .gt => .bvar bvarId.pred -/

def replace.bvar (repl : Expr Γ τ)
    (ΓPre : List _)
    : (Γctx : List _)
    → (n : Fin2 (Γctx ++ [τ] ++ Γ).length)
    → Expr (ΓPre ++ Γctx ++ Γ) ((Γctx ++ [τ] ++ Γ).getFin2 n)
  | [], .fz =>
    have := bvarShift' (Γshift := ΓPre) repl
    cast (congr (congr rfl (congr (congr rfl (List.append_nil _).symm) rfl)) rfl) this
  | [], .fs v =>
    have := bvarShift' (Γshift := ΓPre) $ .bvar (Γ := Γ) v
    cast (congr (congr rfl (List.append_assoc _ _ _).symm) rfl) this
  | hd :: tl, .fz =>
    have := bvarShift' (Γshift := ΓPre)
      $ Expr.bvar (Γ := hd :: tl ++ Γ) (.fz (n := (tl ++ Γ).length))
    cast (congr (congr rfl (List.append_assoc _ _ _).symm) rfl) this
  | hd :: tl, .fs v =>
    have := replace.bvar repl (ΓPre ++ [hd]) tl v
    cast (by congr 2; exact (List.append_cons _ _ _).symm) this

def replace (body : Expr (Γctx ++ [τ] ++ Γ) τo) (repl : Expr Γ τ) : Expr (Γctx ++ Γ) τo := match body with
  | .bvar n => replace.bvar repl [] Γctx n
  | .abs ty body => .abs ty (body.replace (Γctx := ty :: Γctx) repl)

  | .app a b => .app (a.replace repl) (b.replace repl)
  | .eif c t f => .eif (c.replace repl) (t.replace repl) (f.replace repl)
  | .succ v => .succ (v.replace repl)
  | .pred v => .pred (v.replace repl)
  | .fix v => .fix (v.replace repl)
  | .z? v => .z? (v.replace repl)

  | .tt => .tt
  | .ff => .ff
  | .zero => .zero

def β : Expr (τ :: Γ) τo → Expr Γ τ → Expr Γ τo := replace (Γctx := [])

