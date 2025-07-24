import LeanScratch.Fin2

namespace SysF

inductive Ty : Nat → Type
  | var (v : Fin2 n) : Ty n
  | arr (dom ran : Ty n) : Ty n
  | fa (v : Ty n.succ) : Ty n

def vShift
    : {n z : Nat} → Fin2 (n + z) → Fin2 (n.succ + z)
  | _, 0, v => .fs v
  | _, _v+1, .fz => .fz -- For a strange reason if i use _ instead of _v it breaks?
  | _, z+1, .fs v => .fs $ vShift (z := z) v

def Ty.bvarShift : Ty (n + z) → Ty (n.succ + z)
  | .var v => .var (vShift v)
  | .arr a b => .arr a.bvarShift b.bvarShift
  | .fa v => .fa (v.bvarShift (z := z.succ))

def Ty.replace.bvar
    (repl : Ty nAnte)
    (nPre : Nat)
    : (nMid : Nat)
    → (n : Fin2 (nMid + 1 + nAnte))
    → Ty (nPre + nMid + nAnte)
  | _, _ => sorry
  /- | _, 0, .fz, repl   => repl -/
  /- | _, 0, .fs v, repl => .var v -/
  /- | _, z+1, .fs _, _  => sorry -/
  /- | _, z+1, .fz, _    => .var .fz -/

def Ty.replace : Ty (n.succ + z) → Ty n → Ty (n + z)
  | .var v, repl => Ty.replace.bvar v repl
  | .arr a b, repl => .arr (a.replace repl) (b.replace repl)
  | .fa v, repl => .fa $ v.replace (z := z.succ) repl

inductive Expr : {n : Nat} → List (Ty n) → Ty n → Type
  | bvar idx : Expr Γ (Γ.getFin2 idx)
  | abs (ty : Ty n) (body : Expr (ty :: Γ) ret) : Expr Γ (.arr ty ret)
  | app (fn : Expr Γ (.arr arg ret)) (arg : Expr Γ arg) : Expr Γ ret

  | tapp
    {n : Nat} {Γ : List (Ty n)} {body : Ty n.succ}
    (fn : Expr Γ (.fa body)) (t : Ty n)
    : Expr Γ (body.replace (z := 0) t)
  | tabs
    (body : Expr (Γ.map (Ty.bvarShift (z := 0))) ot)
    : Expr Γ (.fa ot)



