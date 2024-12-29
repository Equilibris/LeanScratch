import LeanScratch.Vec
import LeanScratch.LogicProof.FirstOrderLogic.Formula

namespace FOL

def Term.bvarShift (shift skip : ℕ) : Term Arity → Term Arity
  | .var n => .var $ if n < skip then n else n + shift
  | .const nm args => .const nm $ mapper args
    where
      mapper {n} : Vec _ n → Vec _ n
        | hd %:: tl => hd.bvarShift shift skip %:: mapper tl
        | %[] => %[]

/- def Formula.bvarShift (shift skip : ℕ) : Formula TA PA → Formula TA PA
  | .pred nm args => .pred nm (args.map (Term.bvarShift shift skip))

  | .univ f => .univ (bvarShift shift skip.succ f)
  | .exis f => .exis (bvarShift shift skip.succ f)

  | .conj f g => .conj (bvarShift shift skip f) (bvarShift shift skip g)
  | .disj f g => .disj (bvarShift shift skip f) (bvarShift shift skip g)
  | .imp f g => .imp (bvarShift shift skip f) (bvarShift shift skip g)
  | .iff f g => .iff (bvarShift shift skip f) (bvarShift shift skip g)
  | .neg f => .neg (bvarShift shift skip f) -/

def Term.replace.var (bvarId idx_shift : ℕ) (replace : Term Arity) : Term Arity :=
  match compare bvarId idx_shift with
  | .lt => .var bvarId
  | .eq => replace.bvarShift idx_shift 0
  | .gt => .var bvarId.pred

def Term.replace (idx : ℕ) (body replace : Term Arity) : Term Arity := match body with
  | .var n => Term.replace.var n idx replace
  | .const nm args => .const nm $ mapper args
    where
      mapper {n} : Vec _ n → Vec _ n
        | hd %:: tl => hd.replace idx replace %:: mapper tl
        | %[] => %[]

def Formula.replace (idx : ℕ) (body : Formula TA PA) (repl : Term TA) : Formula TA PA := match body with
  | .pred nm args => .pred nm (args.map (·.replace idx repl))

  | .univ f => .univ (f.replace idx.succ repl)
  | .exis f => .exis (f.replace idx.succ repl)

  | .conj a b => .conj (a.replace idx repl) (b.replace idx repl)
  | .disj a b => .disj (a.replace idx repl) (b.replace idx repl)
  | .imp a b => .imp (a.replace idx repl) (b.replace idx repl)
  | .iff a b => .iff (a.replace idx repl) (b.replace idx repl)

  | .neg v => .neg (v.replace idx repl)

def Formula.β (body : Formula TA PA) (repl : Term TA) : Formula TA PA := body.replace 0 repl

