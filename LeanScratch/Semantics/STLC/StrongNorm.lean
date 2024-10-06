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

/- theorem addN_congr_lt_addN -/
/-     {ha : ArgCount (.arr argTy retTy)} -/
/-     {hb hc : ArgCount argTy} -/
/-     (hLt : hb < hc) -/
/-     : (ha hb).addN (naturalize hb + 1) < (ha hc).addN (naturalize hc + 1) := -/
/-   match retTy with -/
/-   | .direct _ => by -/
/-     change lt _ _ -/
/-     simp only [lt, addN, naturalize, Nat.add_eq, ← add_assoc, Nat.lt_eq, add_lt_add_iff_right] -/
/-     sorry -/
/-   | .arr _ _ => by -/
/-     sorry -/

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
theorem upperBoundRed_le_from_lt
  {a b : ArgCount ty}
  {Γ₂' : TyArr Γ₂} (h : a < b)
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
      generalize hEq : idx - Γ₂.length = idx at hTy
      clear *-h
      cases idx
      · simp only [List.getElem?_cons_zero] at hTy
        subst hTy
        simp [TyArr.get]
        sorry
      · sorry
  | .abs _ _ => by
    cases hTy; next ty body retTy hTy =>
    change CTySpec ((ty :: Γ₂) ++ _ :: _) _ _ at hTy
    /- change ArgCount.le _ _ -/
    /- have := upperBoundRed_le_from_lt (Γ₂ := ty :: Γ₂) h hTy -/
    /- change ArgCount.lt _ _ ∨ _ -/
    change le _ _
    simp only [le]
    intro x xmono
    dsimp [upperBoundRed]
    change (upperBoundRed hTy (TyArr.cons x Γ₂' ++ TyArr.cons a Γ'))
        ≤ (upperBoundRed hTy (TyArr.cons x Γ₂' ++ TyArr.cons b Γ'))
    exact upperBoundRed_le_from_lt h hTy
  | .app _ _ => by
    cases hTy; next harg hfn =>
    dsimp [upperBoundRed]
    change le _ _
    simp only [le, addN]
    sorry

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
      intro a b h
      change upperBoundRed _ (TyArr.nil ++ (TyArr.cons _ _)) ≤ upperBoundRed _ (TyArr.nil ++ (TyArr.cons _ _))
      change CTySpec ([] ++ _ :: _) _ _ at hTy
      exact upperBoundRed_le_from_lt h hTy
    · intro x
      dsimp [upperBoundRed]
      sorry
  | .app _ _, .app ha hb => by
    sorry
    /- dsimp [upperBoundRed, Monotonic] -/
    /- stop -/
    /- constructor -/
    /- · sorry -/
    /- · sorry -/
    /- sorry -/
end

open ArgCount in
theorem β_naturalize
    {p₁ : CTySpec Γ (.app (.abs argTy body) arg) t₁}
    {p₂ : CTySpec Γ (body.β arg) t₁}
    : naturalize (upperBoundRed p₂ Γ' ) < naturalize (upperBoundRed p₁ Γ') := by
  dsimp [Stx.β] at p₂
  cases p₁; next pRepl hBody =>
  cases hBody; next hBody =>
  dsimp [upperBoundRed]
  change CTySpec ([] ++ Γ) _ _ at pRepl
  change CTySpec ([] ++ (_ :: Γ)) _ _ at hBody
  obtain ⟨replSz, z⟩ : ∃ replSz, upperBoundRed pRepl Γ' = replSz := exists_eq'
  have := upperBoundRed_eq_replace (Γ₂ := []) (Γ'₂ := .nil) pRepl z hBody p₂
  change upperBoundRed _ (TyArr.cons _ _) = _ at this
  rw [z, this, naturalize_addN, Nat.add_comm (m := 1), ←Nat.add_assoc]
  change _ < (upperBoundRed _ Γ').naturalize + 1 + _
  calc
    _ < _ + 1 := Nat.lt_succ_self _
    _ ≤ _ := Nat.le_add_right _ _

/-- info: 'STLC.β_naturalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms β_naturalize

theorem Red_decn
    (h : Red a b)
    (hTyA : CTySpec Γ a ty) (hTyB : CTySpec Γ b ty)
    : (upperBoundRed hTyB Γ').naturalize < (upperBoundRed hTyA Γ').naturalize := by
  induction h generalizing ty Γ Γ'
  case appl ih =>
    cases hTyA; cases hTyB; next hap hbp _ har hbr =>
    obtain rfl := CTySpec_unique hap har
    obtain rfl := CTySpec_singleton hap har
    simp only [upperBoundRed, Nat.succ_eq_add_one]
    have := ih (Γ' := Γ') hbp hbr
    simp [ArgCount.naturalize_addN]
    sorry
    /- exact addN_lt_addN_right $ ih hbp hbr $ upperBoundRed hap Γ' -/
  case appr ih =>
    cases hTyA; cases hTyB; next hap hbp _ har hbr =>
    obtain ⟨rfl, _⟩ := (Ty.arr.injEq _ _ _ _).mp $ CTySpec_unique hbp hbr
    obtain rfl := CTySpec_singleton hbp hbr
    simp only [upperBoundRed, Nat.succ_eq_add_one]
    have := ih (Γ' := Γ') hap har
    simp [ArgCount.naturalize_addN]
    /- apply addN_lt_addN_left -/
    sorry
    /- exact addN_congr_lt_addN this -/
  case congr aBody bBody ty' subR ih =>
    cases hTyA; cases hTyB; next ha hb =>
    sorry
    /- intro z -/
    /- exact ih ha hb -/
  case beta => exact β_naturalize

theorem STLC.extracted_1
    {ante post top : Stx} {Γ' : TyArr Γ}
    /- (r : Red b b') -/
    (ord : upperBoundRed har Γ' < upperBoundRed hap Γ')
    (hTop : CTySpec Γ top (argTy ⇒ rTy))
    (hAnte : CTySpec Γ ante argTy) 
    (hPost : CTySpec Γ post argTy)
    : upperBoundRed hTop Γ' (upperBoundRed hPost Γ') ≤ upperBoundRed hTop Γ' (upperBoundRed hAnte Γ') :=
  match hTop with
  | .bvar _ => by
    dsimp [upperBoundRed]
    sorry
  | .abs _ => sorry
  | .app _ _ => sorry

open ArgCount in
theorem Red_dec (h : Red a b)
    (hTyA : CTySpec Γ a ty) (hTyB : CTySpec Γ b ty)
    : (upperBoundRed hTyB Γ') < (upperBoundRed hTyA Γ') := by
  induction h generalizing ty Γ Γ'
  case appl ih =>
    cases hTyA; cases hTyB; next hap hbp _ har hbr =>
    obtain rfl := CTySpec_unique hap har
    obtain rfl := CTySpec_singleton hap har
    simp only [upperBoundRed, Nat.succ_eq_add_one]
    exact addN_lt_addN_right $ ih hbp hbr $ upperBoundRed hap Γ'
  case appr ih =>
    cases hTyA; cases hTyB; next hap hbp _ har hbr =>
    obtain ⟨rfl, _⟩ := (Ty.arr.injEq _ _ _ _).mp $ CTySpec_unique hbp hbr
    obtain rfl := CTySpec_singleton hbp hbr
    simp only [upperBoundRed, Nat.succ_eq_add_one]
    specialize (ih (Γ' := Γ') hap har)
    apply le_addN_lt_lt _ (Nat.add_lt_add_right (lt_naturalize ih) 1)
    /- have := upperBoundRed_Monotonic -/
    sorry
  case congr aBody bBody ty' subR ih =>
    cases hTyA; cases hTyB; next ha hb =>
    intro z
    exact ih ha hb
  case beta =>
    exact β_lt

