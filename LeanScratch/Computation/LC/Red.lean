import LeanScratch.Computation.LC.Stx
import LeanScratch.Computation.LC.Beta
import Mathlib.Data.Rel

namespace LC

set_option pp.fieldNotation false in
inductive Red : Stx → Stx → Prop
  | appl  : Red a a' → Red [l|a b] [l|a' b]
  | appr  : Red b b' → Red [l|a b] [l|a b']
  | congr : Red a a' → Red [l|λ. a] [l|λ. a']
  | beta  : Red [l| (λ. body) v] (body.replace 0 v)
  -- Need to make sure 0 is free in body
  /- | eta   : Red (.abs (.app body (.bvar 0))) (body) -/

scoped infix:30 "→ᵣ" => Red
scoped infix:30 "→ᵣ*" => Relation.ReflTransGen Red

def long_appl (h : a →ᵣ* a') : [l|a b] →ᵣ* [l|a' b] := by
  induction h
  case refl => exact .refl
  case tail h ih => exact .tail ih (.appl h)

def long_appr (h : b →ᵣ* b') : [l|a b] →ᵣ* [l|a b'] := by
  induction h
  case refl => exact .refl
  case tail h ih => exact .tail ih (.appr h)

def long_congr (h : b →ᵣ* b') : [l|λ. b] →ᵣ* [l|λ. b'] := by
  induction h
  case refl => exact .refl
  case tail h ih => exact .tail ih (.congr h)

/- instance : Trans R (Relation.ReflTransGen R) (Relation.ReflTransGen R) where -/
/-   trans := sorry -/
/- instance : Trans R R (Relation.ReflTransGen R) where -/
/-   trans := sorry -/
/- instance : Trans (Relation.ReflTransGen R) R (Relation.ReflTransGen R) where -/
/-   trans := sorry -/


