
inductive Ty
  | unit | int | bool

abbrev Ty.denote : Ty → Type
  | .unit => Unit
  | .bool => Bool
  | .int  => Nat

inductive Stx (n : Nat) : Ty → Type
  | add (lhs rhs : Stx n .int) : Stx n .int
  | lt (lhs rhs : Stx n .int) : Stx n .bool
  | var (pt : Fin n) : Stx n .int
  | assign (idx : Fin n) (rest : Stx n .int) : Stx n .unit
  | seq (a : Stx n .unit) (b : Stx n t) : Stx n t
  | eif (c : Stx n .bool) (t f : Stx n v) : Stx n v


abbrev State (n : Nat) := Fin n → Nat
abbrev S (n : Nat) := StateM (State n)

def fixF
    (b : State n → Prop) (c : State n → State n)
    (w : State n → State n) (s : State n)
    [Decidable (b s)]
  : State n := if b s then w (c s) else s

def Stx.denote : Stx n ty → S n ty.denote
  | .add lhs rhs => do
    let lhs ← lhs.denote
    let rhs ← rhs.denote
    return lhs + rhs
  | .lt lhs rhs => do
    let lhs ← lhs.denote
    let rhs ← rhs.denote
    return lhs < rhs
  | .var pt => (· pt) <$> get
  | .assign idx v => do
    let v ← v.denote
    modify (fun x addr => if addr = idx then v else x addr)
    return ()
  | seq a b => do
    a.denote
    b.denote
  | eif c t f => do
    if ← c.denote
    then t.denote
    else f.denote

example : (Stx.add (.add a b) c).denote = (Stx.add a (.add b c)).denote := by
  simp only [Stx.denote, bind_assoc, pure_bind]
  congr
  repeat (funext _; congr 1)
  rw [Nat.add_assoc]
example : (Stx.seq (.seq a b) c).denote = (Stx.seq a (.seq b c)).denote := by
  simp only [Stx.denote, bind_assoc]

/- inductive Stx.denote : (Fin n → Nat) → (Stx n ty) → (Fin n → Nat) → ty.denote → Prop -/
/-   | var : Stx.denote state (.var idx) state (state idx) -/
/-   | add (lhs : Stx.denote s₁ a s₂ av) (rhs : Stx.denote s₂ b s₃ bv) : Stx.denote s₁ (.add a b)  -/


