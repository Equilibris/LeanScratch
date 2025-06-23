import LeanScratch.Fin2
import Mathlib.Data.List.AList

inductive Ty : Type
  | t (n : Nat) : Ty
  | arr : Ty → Ty → Ty
  | var (n : Nat)

namespace Ty

/- abbrev Mapping := AList (fun (_ : Nat) => Nat) -/
/- def equiv (m : Mapping) : Ty → Ty → Prop -/

inductive Check (f : Nat → Nat) : Ty → Ty → Prop
  | t : Check f (t n) (t n)
  | arr : Check f a₁ a₂ → Check f b₁ b₂ → Check f (arr a₁ b₁) (arr a₂ b₂)
  | var : Check f (var n) (var $ f n)

def Equiv (a b : Ty) : Prop := ∃ f, Function.Bijective f → Check f a b

def value : Ty → Nat
  | t _ => 0
  | var v => v.succ
  | arr a b => a.value + 2 * b.value

end Ty

inductive Stx : Nat → Type
  | abs (ty : Option Ty) (body : Stx n.succ) : Stx n
  | app (a b : Stx n) : Stx n
  | bvar : Fin2 n → Stx n



