
inductive Ty
  | nat
  | arrow (a b : Ty)

mutual
inductive Val : List Ty → Ty → Type
  | z : Val Γ .nat
  | s : Val Γ .nat → Val Γ .nat
  | bvar idx : Val Γ (Γ.get idx)
  | abs (ty : Ty) (body : Expr (ty :: Γ) ret) : Val Γ (.arrow ty ret)

inductive Expr : List Ty → Ty → Type
  | app  (fn : Val Γ (.arrow arg ret)) (arg : Val Γ arg) : Expr Γ ret
  | lete (bd : Val (arg :: Γ) ret) (e : Val Γ arg) : Expr Γ ret
  | rece (n : Val Γ .nat) (z : Val Γ τ ) (s : Val Γ (.arrow τ τ)) : Expr Γ τ
end

def Val.bvarShift : Val (Γskip ++ Γ₁) τ → Val (Γskip ++ Γshift ++ Γ₁) τ
  | .bvar n =>
    cast (congr rfl Fin.extend.eq.symm) $ .bvar (Fin.castAdd n)
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



