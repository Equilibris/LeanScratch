import LeanScratch.Vec

namespace FOL

inductive Term {Nm : Type} (Vars : Nat) (Arity : Nm → Nat)
  | var   (idx : Fin2 Vars) -- These are no longer De Bujin index, now they simply identify vars
  | const (nm : Nm) (app : Vec (Term Vars Arity) (Arity nm))

inductive Formula {TNm PNm : Type} (TA : TNm → Nat) (PA : PNm → Nat) : Nat → Type 1
  | pred (nm : PNm) (app : Vec (Term Vars TA) (PA nm)) : Formula TA PA Vars

  -- We use non-parametric HOS to get around substitution issues
  | univ : (∀ Vars, Term Vars TA → Formula TA PA Vars) → Formula TA PA Vars
  | exis : (∀ Vars, Term Vars TA → Formula TA PA Vars) → Formula TA PA Vars

  | conj : Formula TA PA Vars → Formula TA PA Vars → Formula TA PA Vars
  | disj : Formula TA PA Vars → Formula TA PA Vars → Formula TA PA Vars
  | imp  : Formula TA PA Vars → Formula TA PA Vars → Formula TA PA Vars
  | iff  : Formula TA PA Vars → Formula TA PA Vars → Formula TA PA Vars
  | neg  : Formula TA PA Vars → Formula TA PA Vars

def Term.lift : Term Vars Arity → Term (Vars + 1) Arity
  | .var idx => .var $ idx.castSucc
  | .const nm args => .const nm $ mapper args
    where
      mapper {n} : Vec _ n → Vec _ n
        | %[] => %[]
        | hd %:: tl => hd.lift %:: mapper tl

def Formula.lift : Formula TA PA Vars → Formula TA PA (Vars + 1)
  | .pred nm args => sorry

  | .univ x => .univ (x ·)
  | .exis x => .univ (x ·)

  | .conj a b => .conj a.lift b.lift
  | .disj a b => .disj a.lift b.lift
  | .imp  a b => .imp  a.lift b.lift
  | .iff  a b => .iff  a.lift b.lift
  | .neg v => .neg v.lift

