import LeanScratch.Semantics.STLC.Stx
import LeanScratch.Semantics.STLC.Red
import LeanScratch.Semantics.STLC.Typed
import LeanScratch.Semantics.STLC.Infer
import LeanScratch.Semantics.STLC.StrongNorm.CTySpec
import LeanScratch.Semantics.STLC.StrongNorm.ArgCount
import LeanScratch.Semantics.STLC.StrongNorm.TyArr
import LeanScratch.Semantics.STLC.StrongNorm.upperBoundRed
import LeanScratch.ListUtils

/-

# Possible ways to solve strong normalization of STLC

What does it mean for something to happen 'eventually'

1.  [ ] Encode terms as ordinals
2.  [ ] Simple structural recursion
3.  [ ] Number of unique types decrease
4.  [ ] Encode problem as a graph, prove there are no infinite paths + cycles
5.  [ ] Number of bound variables
6.  [ ] Number of lambdas
7.  [ ] Maximum bound variable decreases (eventually?)
8.  [ ] Locations where a function can be applied decreases
9.  [ ] Any of the above apply on a congruence level - what does this mean
10. [ ] A solution either decreases the maximum bvar, or it removes one bvar below it
11. [ ] 'Negative bvars' are bound variables simply used within an
        expression, number of 'negative bvars decrease'
12. [ ] Do any of these metrics even matter on an application level?
13. [ ] Eventually the smallest negative bvar has to be reduced
14. [ ] A vector of negative bvars and occurances of said negative bvars decrease
15. [ ] The negative bvar vector looks like a CNF-ordinal
16. [ ] The types get less arrows in them in total
17. [ ] The level of congruance application (eventually) decreases this relates
18. [ ] Either types will stick around, or they will (eventually) be removed
19. [ ] Types of lambdas cannot be created, only destroyed
20. [ ] Number of 'hot applications' decreases, number of applications
        with a lambda at some point on the left
21. [ ] If any of the above hold for any sub-expression (like a lhs)
        and for a (rhs) we can dictate they might hold for the whole expr
22. [ ] Reducability decrease, this tracks how many lambdas / bvars
        are on the left hand side of an expression
23. [ ] 
24. [ ] 
25. [ ] 
26. [ ] 
27. [ ] 

-/

namespace STLC

open ArgCount in
theorem β_lt
    {p₁ : CTySpec Γ (.app (.abs argTy body) arg) t₁}
    {p₂ : CTySpec Γ (body.β arg) t₁}
    : (upperBoundRed p₂ Γ' ) < (upperBoundRed p₁ Γ') := by
  dsimp [Stx.β] at p₂
  cases p₁; next pRepl hBody =>
  cases hBody; next hBody =>
  dsimp [upperBoundRed]
  change CTySpec ([] ++ Γ) _ _ at pRepl
  change CTySpec ([] ++ (_ :: Γ)) _ _ at hBody
  obtain ⟨replSz, z⟩ : ∃ replSz, upperBoundRed pRepl Γ' = replSz := exists_eq'
  have := upperBoundRed_eq_replace (Γ₂ := []) (Γ'₂ := .nil) pRepl z hBody p₂
  change upperBoundRed _ (TyArr.cons _ _) = _ at this
  rw [z, this]
  apply self_lt_addN
  exact Nat.zero_lt_succ _

open ArgCount in
mutual
theorem upperBoundRed_le_from_le
  {a b : ArgCount ty} {Γ' : TyArr Γ}
  {Γ₂' : TyArr Γ₂}
  (h : a ≤ b)
  (hΓ' : TyArr.Every Monotonic Γ')
  (aMono : Monotonic a)
  (bMono : Monotonic b)
  (hΓ₂' : TyArr.Every Monotonic Γ₂')
  (hTy : CTySpec (Γ₂ ++ (ty :: Γ)) body retTy)
  : (upperBoundRed hTy (Γ₂' ++ TyArr.cons a Γ')
    ≤ upperBoundRed hTy (Γ₂' ++ TyArr.cons b Γ'))
    :=
  match body with
  | .bvar _ => by
    cases hTy; next idx hTy =>
    dsimp [upperBoundRed]
    by_cases hLtIdx : idx < Γ₂.length
    · rw [List.getElem?_append hLtIdx] at hTy
      rw [TyArr.get_append hTy, TyArr.get_append hTy]
      exact self_le_self
    · rw [not_lt] at hLtIdx
      rw [List.getElem?_append_right hLtIdx] at hTy
      rw [TyArr.get_append_right hLtIdx hTy, TyArr.get_append_right hLtIdx hTy]
      generalize idx - Γ₂.length = idx at hTy
      clear *-h
      cases idx
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hTy
        subst hTy
        simp only [TyArr.get, cast_eq]
        exact h
      · exact self_le_self
  | .abs _ _ => by
    cases hTy; next ty body retTy hTy =>
    change CTySpec ((ty :: Γ₂) ++ _ :: _) _ _ at hTy
    change le _ _
    simp only [le]
    intro x xm
    dsimp [upperBoundRed]
    change (upperBoundRed hTy (TyArr.cons x Γ₂' ++ TyArr.cons a Γ'))
        ≤ (upperBoundRed hTy (TyArr.cons x Γ₂' ++ TyArr.cons b Γ'))
    exact upperBoundRed_le_from_le h hΓ' aMono bMono (.cons xm hΓ₂') hTy
  | .app _ _ => by
    cases hTy; next harg hfn =>
    dsimp [upperBoundRed]
    change le _ _
    have hArg : (upperBoundRed harg (Γ₂' ++ TyArr.cons a Γ')) ≤ (upperBoundRed harg (Γ₂' ++ TyArr.cons b Γ')) :=
      upperBoundRed_le_from_le h hΓ' aMono bMono hΓ₂' _
    have hFn  : (upperBoundRed hfn (Γ₂' ++ TyArr.cons a Γ')) ≤ (upperBoundRed hfn (Γ₂' ++ TyArr.cons b Γ')) :=
      upperBoundRed_le_from_le h hΓ' aMono bMono hΓ₂' _
    have fnAMono : (upperBoundRed hfn (Γ₂' ++ TyArr.cons a Γ')).Monotonic :=
      upperBoundRed_Monotonic (TyArr.Every_concat hΓ₂' (.cons aMono hΓ'))
    have argAMono : (upperBoundRed harg (Γ₂' ++ TyArr.cons a Γ')).Monotonic :=
      upperBoundRed_Monotonic (TyArr.Every_concat hΓ₂' (.cons aMono hΓ'))
    have argBMono : (upperBoundRed harg (Γ₂' ++ TyArr.cons b Γ')).Monotonic :=
      upperBoundRed_Monotonic (TyArr.Every_concat hΓ₂' (.cons bMono hΓ'))

    generalize /- hFnA :  -/ upperBoundRed hfn (Γ₂' ++ TyArr.cons a Γ') = fnA at *
    generalize /- hFnB :  -/ upperBoundRed hfn (Γ₂' ++ TyArr.cons b Γ') = fnB at *
    generalize /- hArgA : -/ upperBoundRed harg (Γ₂' ++ TyArr.cons a Γ') = argA at *
    generalize /- hArgB : -/ upperBoundRed harg (Γ₂' ++ TyArr.cons b Γ') = argB at *

    exact le_trans
      (addN_le_addN_right (le_congr fnAMono argAMono argBMono hFn hArg))
      (addN_le_addN_left (Nat.succ_le_succ (le_naturalize hArg)))

theorem upperBoundRed_Monotonic
    {Γ' : TyArr Γ} {hTy : CTySpec Γ body ty}
    (hPrevHolds : TyArr.Every Monotonic Γ')
    : Monotonic (upperBoundRed hTy Γ') :=
  match body, hTy with
  | .bvar _, .bvar hTy => TyArr.Every_get hPrevHolds
  | .abs _ _, .abs hTy => by
    simp only [Monotonic]
    constructor
    · dsimp [upperBoundRed]
      intro a b aMono bMono h
      change upperBoundRed _ (TyArr.nil ++ (TyArr.cons _ _)) ≤ upperBoundRed _ (TyArr.nil ++ (TyArr.cons _ _))
      change CTySpec ([] ++ _ :: _) _ _ at hTy
      exact upperBoundRed_le_from_le h hPrevHolds aMono bMono .nil hTy
    · intro x xm
      exact upperBoundRed_Monotonic (.cons xm hPrevHolds)
  | .app _ _, .app ha hb => by
    dsimp [upperBoundRed, Monotonic, addN]
    apply addN_Monotonic
    have x : Monotonic (upperBoundRed ha _) := upperBoundRed_Monotonic hPrevHolds
    simp only [Monotonic] at x
    rcases x with ⟨_, haMR⟩
    exact haMR (upperBoundRed hb Γ') (upperBoundRed_Monotonic hPrevHolds)
end

open ArgCount in
theorem Red_dec
    {Γ' : TyArr Γ}
    (every : TyArr.Every Monotonic Γ')
    (h : Red a b)
    (hTyA : CTySpec Γ a ty) (hTyB : CTySpec Γ b ty)
    : (upperBoundRed hTyB Γ') < (upperBoundRed hTyA Γ') := by
  induction h generalizing ty Γ Γ'
  case appl ih =>
    cases hTyA; cases hTyB; next hap hbp _ har hbr =>
    obtain rfl := CTySpec_unique hap har
    obtain rfl := CTySpec_singleton hap har
    simp only [upperBoundRed, Nat.succ_eq_add_one]
    exact addN_lt_addN_right 
      $ lt_sufficency (upperBoundRed_Monotonic every)
      $ ih every hbp hbr
  case appr ih =>
    cases hTyA; cases hTyB; next hap hbp _ har hbr =>
    obtain ⟨rfl, _⟩ := (Ty.arr.injEq _ _ _ _).mp $ CTySpec_unique hbp hbr
    obtain rfl := CTySpec_singleton hbp hbr
    simp only [upperBoundRed, Nat.succ_eq_add_one]
    specialize (ih (Γ' := Γ') every hap har)
    have m : Monotonic (upperBoundRed hbp Γ') := upperBoundRed_Monotonic every
    simp only [Monotonic] at m
    have := m.1 _ _ (upperBoundRed_Monotonic every) (upperBoundRed_Monotonic every) (le_of_lt ih)
    exact le_trans_lt
      (addN_le_addN_right this)
      $ addN_lt_addN_left
      $ Nat.add_one_lt_add_one_iff.mpr (lt_naturalize ih)
  case congr aBody bBody ty' _ ih =>
    cases hTyA; cases hTyB; next ha hb =>
    intro z zMono
    exact ih (.cons zMono every) ha hb
  case beta =>
    exact β_lt

/-- info: 'STLC.Red_dec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Red_dec

open ArgCount in
theorem Red_nat_dec
    {Γ' : TyArr Γ}
    (every : TyArr.Every Monotonic Γ')
    (h : Red a b)
    (hTyA : CTySpec Γ a ty) (hTyB : CTySpec Γ b ty)
    : (upperBoundRed hTyB Γ').naturalize < (upperBoundRed hTyA Γ').naturalize := lt_naturalize (Red_dec every h hTyA hTyB)

open ArgCount in
theorem RedPlus_nat_dec
    {Γ' : TyArr Γ}
    (every : TyArr.Every Monotonic Γ')
    (h : RedPlus a b)
    (hTyA : CTySpec Γ a ty) (hTyB : CTySpec Γ b ty)
    : (upperBoundRed hTyB Γ').naturalize < (upperBoundRed hTyA Γ').naturalize := by
  induction h
  case single a => exact Red_nat_dec every a hTyA hTyB
  case tail b c redPlus red ih =>
    have := TySpec_CTySpec $ LongTypePreservation (CTySpec_TySpec hTyA) (Relation.TransGen.to_reflTransGen redPlus)
    exact lt_trans (Red_nat_dec every red this hTyB) (ih this)

inductive ReflTransCount (R : a → a → Prop) : a → a → ℕ → Prop
  | refl : ReflTransCount R x x 0
  | tail : ReflTransCount R x y n → R y z → ReflTransCount R x z n.succ

