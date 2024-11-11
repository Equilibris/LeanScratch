import LeanScratch.Semantics.STLC.Stx

namespace STLC.Stx

def bvarShift (shift skip : ℕ) : Stx → Stx
  | .bvar n => .bvar $ if n < skip then n else n + shift
  | .app a b => .app (a.bvarShift shift skip) (b.bvarShift shift skip)
  | .abs ty body => .abs ty (body.bvarShift shift skip.succ)

def replace.bvar (bvarId idx_shift : ℕ) (replace : Stx) : Stx :=
  match compare bvarId idx_shift with
  | .lt => .bvar bvarId
  | .eq => replace.bvarShift idx_shift 0
  | .gt => .bvar bvarId.pred

-- Replace also needs to add idx to every value within replace to ensure that the binders still point towards the right points
def replace (idx_shift : ℕ) (body replace : Stx) : Stx := match body with
  | .bvar n => Stx.replace.bvar n idx_shift replace
  | .app fn arg => .app (fn.replace idx_shift replace) (arg.replace idx_shift replace)
  | .abs ty v => .abs ty (v.replace idx_shift.succ replace)

def β (body repl : Stx) : Stx := (body.replace 0 repl)
