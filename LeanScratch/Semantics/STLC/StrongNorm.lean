import LeanScratch.Semantics.STLC.Stx
import LeanScratch.Semantics.STLC.Red
import LeanScratch.Semantics.STLC.Typed
import LeanScratch.Semantics.STLC.Infer
import LeanScratch.Semantics.STLC.StrongNorm.CTySpec
import LeanScratch.Semantics.STLC.StrongNorm.ArgCount
import LeanScratch.Semantics.STLC.StrongNorm.TyArr
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
def upperBoundRed
    {x : Stx} (hTy : CTySpec Γ x ty)
    (v : TyArr Γ) : ArgCount ty :=
  match x, hTy with
  | .bvar _, .bvar hTy => TyArr.get hTy v
  | .abs _ _, .abs hTy => fun z => upperBoundRed hTy $ .cons z v
  | .app _ _, .app ha hb =>
    let ha := upperBoundRed ha v
    let hb := upperBoundRed hb v
    addN (ha hb) (naturalize hb).succ

open ArgCount in
theorem upperBoundRed_eq_replace.bvarShift
    {repl : Stx} {t' : Ty}
    {Γ' : TyArr Γ} {Γ'₂ : TyArr Γ₂}  {Γ'₃ : TyArr Γ₃}
    (pRepl : CTySpec (Γ₃ ++ Γ) repl t')
    (hRepl : CTySpec (Γ₃ ++ Γ₂ ++ Γ) (Stx.bvarShift Γ₂.length Γ₃.length repl) t')
    : upperBoundRed pRepl (Γ'₃ ++ Γ') = upperBoundRed hRepl (Γ'₃ ++ Γ'₂ ++ Γ') :=
  match repl with
  | .bvar idx => by
    dsimp [Stx.bvarShift] at hRepl
    cases pRepl; cases hRepl; next pRepl hRepl =>
    dsimp [upperBoundRed]
    split at hRepl
    <;> rename_i hRepl' h
    · have : (if idx < Γ₃.length then idx else idx + Γ₂.length) = idx := by simp only [h, ↓reduceIte]
      rw [TyArr.get_idx_eq_jdx hRepl this]
      clear *-h
      rw [List.append_assoc _ _ _] at hRepl
      rw [TyArr.get_append_assoc hRepl]
      rw [List.getElem?_append h] at pRepl hRepl
      rw [TyArr.get_append hRepl, TyArr.get_append hRepl]
    · have : (if idx < Γ₃.length then idx else idx + Γ₂.length) = idx + Γ₂.length := by simp only [h, ↓reduceIte]
      rw [TyArr.get_idx_eq_jdx hRepl this]
      clear *-h
      rw [not_lt] at h

      rw [List.append_assoc _ _ _] at hRepl
      rw [TyArr.get_append_assoc hRepl]
      rw [List.getElem?_append_right h] at pRepl
      have := h.trans (Nat.le_add_right idx Γ₂.length)
      rw [List.getElem?_append_right this] at hRepl
      rw [TyArr.get_append_right this hRepl, TyArr.get_append_right h pRepl]
      clear *-h
      have : idx + Γ₂.length - Γ₃.length = idx - Γ₃.length + Γ₂.length := Nat.sub_add_comm h
      rw [this] at hRepl
      rw [TyArr.get_idx_eq_jdx hRepl this]
      rw [List.getElem?_append_right (Nat.le_add_left Γ₂.length (idx - Γ₃.length))] at hRepl
      rw [TyArr.get_append_right (Nat.le_add_left Γ₂.length (idx - Γ₃.length)) hRepl]
      have : idx - Γ₃.length + Γ₂.length - Γ₂.length = idx - Γ₃.length := Nat.add_sub_self_right (idx - Γ₃.length) Γ₂.length
      rw [this] at hRepl
      rw [TyArr.get_idx_eq_jdx hRepl this]
  | .abs ty body => by
    dsimp [Stx.bvarShift] at hRepl
    cases pRepl; cases hRepl; next pArg hBody =>
    dsimp [upperBoundRed]
    funext z
    change CTySpec ((ty :: Γ₃) ++ Γ) _ _ at pArg
    change CTySpec ((ty :: Γ₃) ++ Γ₂ ++ Γ) _ _ at hBody
    change upperBoundRed _ ((TyArr.cons z Γ'₃) ++ Γ')
      = upperBoundRed _ ((TyArr.cons z Γ'₃) ++ Γ'₂ ++ Γ')
    exact upperBoundRed_eq_replace.bvarShift pArg hBody
  | .app a b => by
    dsimp [Stx.bvarShift] at hRepl
    cases pRepl; cases hRepl; next hap hbp _ har hbr =>
    obtain rfl := TySpec_unique (bvarShift_maintain_gen (CTySpec_TySpec hap)) (CTySpec_TySpec har)
    dsimp [upperBoundRed]
    rw [upperBoundRed_eq_replace.bvarShift hap har, upperBoundRed_eq_replace.bvarShift hbp hbr]

open ArgCount in
theorem upperBoundRed_eq_replace.bvar {Γ₂ Γ : List Ty} {repl : Stx} {t' : Ty} {Γ' : TyArr Γ} {replSz : ArgCount t'} {t : Ty}
    {Γ'₂ : TyArr Γ₂} (pRepl : CTySpec Γ repl t') (z : upperBoundRed pRepl Γ' = replSz) (idx : ℕ)
    (h : CTySpec (Γ₂ ++ t' :: Γ) (Stx.bvar idx) t)
    (hRepl :
      CTySpec (Γ₂ ++ Γ)
        (match compare idx Γ₂.length with
        | Ordering.lt => Stx.bvar idx
        | Ordering.eq => Stx.bvarShift Γ₂.length 0 repl
        | Ordering.gt => Stx.bvar (idx - 1))
        t) :
    upperBoundRed h (Γ'₂ ++ TyArr.cons replSz Γ') = upperBoundRed hRepl (Γ'₂ ++ Γ') := by
  split at hRepl
  <;> dsimp only at hRepl
  <;> rename_i hOrd
  <;> simp only [Nat.compare_eq_eq, Nat.compare_eq_lt, Nat.compare_eq_gt] at hOrd
  case h_1 => 
    cases h; cases hRepl; next h hRepl =>
    dsimp [upperBoundRed]
    have : Γ₂[idx]? = some t := by rw [←hRepl, List.getElem?_append hOrd]
    rw [TyArr.get_append this, TyArr.get_append this]
  case h_3 =>
    cases h; cases hRepl; next h hRepl =>
    dsimp [upperBoundRed]
    have : Γ₂.length ≤ idx := Nat.le_of_succ_le hOrd
    rw [List.getElem?_append_right this] at h
    rw [TyArr.get_append_right this h]
    have : Γ₂.length ≤ idx - 1 := Nat.le_sub_one_of_lt hOrd
    rw [List.getElem?_append_right this] at hRepl
    rw [TyArr.get_append_right this hRepl]
    change ([t'] ++ Γ)[_]? = _ at h
    change TyArr.get h ((TyArr.cons replSz .nil) ++ Γ') = _
    clear *-hOrd z
    have : [t'].length ≤ idx - Γ₂.length := Nat.le_sub_of_add_le' hOrd
    rw [List.getElem?_append_right this] at h
    rw [TyArr.get_append_right this h]
    have : idx - Γ₂.length - [t'].length = idx - 1 - Γ₂.length := by
      dsimp only [List.length_singleton]
      rw [Nat.sub_right_comm]
    rw [this] at h
    rw [TyArr.get_idx_eq_jdx h this]
  · cases h; next h =>
    subst hOrd
    dsimp [upperBoundRed]
    rw [List.getElem?_append_right (le_refl _)] at h
    rw [TyArr.get_append_right (le_refl _) h]
    have : Γ₂.length - Γ₂.length = 0 := Nat.sub_self Γ₂.length
    rw [this] at h
    rw [TyArr.get_idx_eq_jdx h this]
    simp only [List.getElem?_cons_zero, Option.some_inj] at h
    subst h
    simp only [TyArr.get, cast_eq]
    rw [←z]
    clear *-
    change CTySpec ([] ++ Γ) _ _ at pRepl
    change CTySpec ([] ++ Γ₂ ++ Γ) (Stx.bvarShift _ ([] : List Ty).length _) _ at hRepl
    change upperBoundRed _ (TyArr.nil ++ Γ') = upperBoundRed _ (TyArr.nil ++ Γ'₂ ++ Γ')
    exact upperBoundRed_eq_replace.bvarShift pRepl hRepl

open ArgCount in
theorem upperBoundRed_eq_replace
    {Γ'₂ : TyArr Γ₂}
    (pRepl : CTySpec Γ repl t')
    (z : upperBoundRed pRepl Γ' = replSz)
    (h : CTySpec (Γ₂ ++ (t' :: Γ)) s t)
    (hRepl : CTySpec (Γ₂ ++ Γ) (Stx.replace (Γ₂.length) s repl) t)
    : upperBoundRed h (Γ'₂ ++ (TyArr.cons replSz Γ')) = upperBoundRed hRepl (Γ'₂ ++ Γ') :=
  match s with
  -- For some reason I need to extract this into its own function.
  -- Unknown why
  | .bvar idx => upperBoundRed_eq_replace.bvar pRepl z idx h hRepl
  | .abs ty body => by
    dsimp [Stx.replace] at hRepl
    cases h; cases hRepl; next h hRepl =>
    dsimp [upperBoundRed]
    apply funext
    intro x
    rw [TyArr.cons_append]
    dsimp [←List.cons_append] at h hRepl
    exact upperBoundRed_eq_replace pRepl z h hRepl
  | .app a b => by
    cases h; cases hRepl; next hb ha _ hbRepl haRepl =>
    simp only [upperBoundRed]
    obtain rfl := ((Ty.arr.injEq _ _ _ _).mp
      $ TySpec_unique
      (CTySpec_TySpec haRepl)
      (TySpec_replace_gen (x := t') (CTySpec_TySpec pRepl) (CTySpec_TySpec ha))).1
    rw [upperBoundRed_eq_replace pRepl z ha haRepl,
        upperBoundRed_eq_replace pRepl z hb hbRepl]

/-- info: 'STLC.upperBoundRed_eq_replace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms upperBoundRed_eq_replace

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
    cases hTy; next id hTy =>
    sorry
  | .abs _ _ => by
    cases hTy; next ty body retTy hTy =>
    change CTySpec ((ty :: Γ₂) ++ _ :: _) _ _ at hTy
    /- change ArgCount.le _ _ -/
    /- have := upperBoundRed_le_from_lt (Γ₂ := ty :: Γ₂) h hTy -/
    /- change ArgCount.lt _ _ ∨ _ -/
    intro x
    dsimp [upperBoundRed]
    change (upperBoundRed hTy (TyArr.cons x Γ₂' ++ TyArr.cons a Γ'))
        ≤ (upperBoundRed hTy (TyArr.cons x Γ₂' ++ TyArr.cons b Γ'))
    exact upperBoundRed_le_from_lt h hTy
  | .app _ _ => by
    cases hTy; next harg hfn =>
    dsimp [upperBoundRed]
    sorry

theorem upperBoundRed_Monotonic
    {Γ' : TyArr Γ} {hTy : CTySpec Γ body ty}
    (hPrevHolds : TyArr.Every Monotonic Γ')
    : Monotonic (upperBoundRed hTy Γ') :=
  match body, hTy with
  | .bvar _, .bvar hTy => TyArr.Every_get hPrevHolds
  | .abs _ _, .abs hTy => by
    constructor
    · dsimp [upperBoundRed]
      intro a b h
      sorry
      /- change upperBoundRed _ (TyArr.nil ++ (TyArr.cons _ _)) ≤ upperBoundRed _ (TyArr.nil ++ (TyArr.cons _ _)) -/
      /- change CTySpec ([] ++ _ :: _) _ _ at hTy -/
      /- exact upperBoundRed_le_from_lt h hTy -/
    · intro x
      dsimp [upperBoundRed]
      sorry
  | .app _ _, .app ha hb => by
    dsimp [upperBoundRed, Monotonic]
    stop
    constructor
    · sorry
    · sorry
    sorry
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

