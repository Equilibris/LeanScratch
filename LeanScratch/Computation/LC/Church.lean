import LeanScratch.Computation.LC.Stx
import LeanScratch.Computation.LC.Beta
import LeanScratch.Computation.LC.Red

namespace LC

def church (n : Nat) : Stx :=
  [l|λ. λ. !(body n)]
where
  body : _ → _
    | 0 => [l|0]
    | n+1 => [l|1 !(body n)]

/- syntax "!n" num : stx_dbIdx -/
/- syntax "!n" ident : stx_dbIdx -/

/- macro_rules -/
/-   | `([l $_t $_ids*| !n$v:num  ]) => `(church $v) -/
/-   | `([l $_t $_ids*| !n$v:ident]) => `(church $v) -/

namespace church

def succ : Stx := [l|λnum f x. f ((num f) x)]

def succ.unfold : [l|succ !(church n)] →ᵣ* (church $ n+1) := calc
  _ →ᵣ* _ := .single .beta
  _ →ᵣ* _ := by
    simp [church, body, Stx.shift]


