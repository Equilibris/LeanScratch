import Mathlib.Data.Nat.PSub
import Mathlib.Data.Rel
import Mathlib.Data.Finset.Basic

inductive Stx
  | bvar  (idx : ℕ)
  | const (n   : ℕ)
  | prod : Stx → Stx → Stx
  | add  : Stx → Stx → Stx
  | sigma (range : Stx) (body : Stx)

def Stx.replace (idx : ℕ) : Stx → Stx → Stx
  | .const n  , _    => .const n
  | .bvar jdx , repl => if idx = jdx then repl else .bvar jdx
  | .sigma r b, repl => .sigma (r.replace idx repl) (b.replace idx.succ repl)
  | .add a b  , repl => .add (a.replace idx repl) (b.replace idx repl)
  | .prod a b , repl => .prod (a.replace idx repl) (b.replace idx repl)

