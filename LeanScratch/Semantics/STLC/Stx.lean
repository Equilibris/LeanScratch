import Mathlib.Data.Nat.PSub
import Mathlib.Data.Rel
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Util.WhatsNew

namespace STLC

inductive Ty
  | direct (id : ℕ)   -- a unique type
  | arr (fn arg : Ty) -- a function type
deriving DecidableEq

infixr:30 " ⇒ " => Ty.arr
prefix:30 "↑" => Ty.direct

inductive Stx
  | bvar (id : ℕ)
  | app  (fn arg : Stx)
  | abs  (ty : Ty) (body : Stx)
deriving DecidableEq

/- scoped prefix:30 "λ: " => Stx.abs -/
/- scoped prefix:30 "b:" => Stx.bvar -/
/- scoped infixl:30 " @ " => Stx.app -/

namespace Stx

