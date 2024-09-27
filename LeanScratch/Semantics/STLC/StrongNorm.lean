import LeanScratch.Semantics.STLC.Stx
import LeanScratch.Semantics.STLC.Red
import LeanScratch.Semantics.STLC.Typed
import LeanScratch.Semantics.STLC.Infer
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

/- inductive TypeCount (t : Ty) : List Ty → Stx → ℕ → Prop -/
/-   | absEq  : TypeCount t (t :: ls)  body n            → TypeCount t ls (.abs t body ) n.succ -/
/-   | absNeq : t' ≠ t → TypeCount t (t' :: ls) body n   → TypeCount t ls (.abs t' body) n -/
/-   | app  : TypeCount t ls a n → TypeCount t ls b k    → TypeCount t ls (.app a b) (n + k) -/
/-   | beq  : ls[i]? = .some t                           → TypeCount t ls (.bvar i) 1 -/
/-   | bneq : ls[i]? ≠ .some t                           → TypeCount t ls (.bvar i) 0 -/

/- def typeCount (t : Ty) (ls : List Ty) : Stx → ℕ -/
/-   | .abs ty body => (typeCount t (ty :: ls) body) + (if ty = t then 1 else 0) -/
/-   | .app a b => (typeCount t ls a) + (typeCount t ls b) -/
/-   | .bvar i => if ls[i]? = .some t then 1 else 0 -/

/- theorem typeCount_TypeCount : typeCount t ls s = n ↔ TypeCount t ls s n := match s with -/
/-   | .abs ty body => by -/
/-     constructor -/
/-     <;> intro h -/
/-     · dsimp [typeCount] at h -/
/-       split at h -/
/-       next hz => -/
/-         obtain ⟨w, p⟩ : ∃ n', typeCount t (ty :: ls) body = n' := exists_eq' -/
/-         rw [p ] at h -/
/-         rw [hz] at p ⊢ -/
/-         rw [←h] -/
/-         exact .absEq (typeCount_TypeCount.mp p) -/
/-       next hz => exact .absNeq hz (typeCount_TypeCount.mp h) -/
/-     · rcases h with (h|h) -/
/-       · rename_i n -/
/-         simp only [typeCount, ↓reduceIte, Nat.succ_eq_add_one, add_left_inj] -/
/-         exact typeCount_TypeCount.mpr h -/
/-       next hz => -/
/-         simp [typeCount] -/
/-         split -/
/-         · contradiction -/
/-         · dsimp -/
/-           exact typeCount_TypeCount.mpr hz -/
/-   | .app a b => by -/
/-     constructor -/
/-     <;> intro h -/
/-     · dsimp [typeCount] at h -/
/-       obtain ⟨an, ap⟩ : ∃ n', typeCount t ls a = n' := exists_eq' -/
/-       obtain ⟨bn, bp⟩ : ∃ k', typeCount t ls b = k' := exists_eq' -/
/-       rw [ap, bp] at h -/
/-       rw [←h] -/
/-       exact .app (typeCount_TypeCount.mp ap) (typeCount_TypeCount.mp bp) -/
/-     · cases h -/
/-       next n k a b => -/
/-       dsimp [typeCount] -/
/-       rw [(typeCount_TypeCount).mpr a, typeCount_TypeCount.mpr b] -/
/-   | .bvar id => by -/
/-     constructor -/
/-     <;> intro h -/
/-     · dsimp [typeCount] at h -/
/-       split at h -/
/-       <;> rw [←h] -/
/-       next hz => exact .beq  hz -/
/-       next hz => exact .bneq hz -/
/-     · cases h <;> simpa [typeCount] -/

namespace Counting

inductive TypeCount (t : Ty) : List Ty → Stx → ℕ → Prop
  | absEq  : TypeCount t (t :: ls)  body n            → TypeCount t ls (.abs t body ) n.succ
  | absNeq : t' ≠ t → TypeCount t (t' :: ls) body n   → TypeCount t ls (.abs t' body) n
  | app  : TypeCount t ls a n → TypeCount t ls b k    → TypeCount t ls (.app a b) (n + k)
  | bvar :                                              TypeCount t ls (.bvar i) 0

def typeCount (t : Ty) (ls : List Ty) : Stx → ℕ
  | .abs ty body => (typeCount t (ty :: ls) body) + (if ty = t then 1 else 0)
  | .app a b => (typeCount t ls a) + (typeCount t ls b)
  | .bvar _ => 0

theorem typeCount_TypeCount : typeCount t ls s = n ↔ TypeCount t ls s n := match s with
  | .abs ty body => by
    constructor
    <;> intro h
    · dsimp [typeCount] at h
      split at h
      next hz =>
        obtain ⟨w, p⟩ : ∃ n', typeCount t (ty :: ls) body = n' := exists_eq'
        rw [p ] at h
        rw [hz] at p ⊢
        rw [←h]
        exact .absEq (typeCount_TypeCount.mp p)
      next hz => exact .absNeq hz (typeCount_TypeCount.mp h)
    · rcases h with (h|h)
      · rename_i n
        simp only [typeCount, ↓reduceIte, Nat.succ_eq_add_one, add_left_inj]
        exact typeCount_TypeCount.mpr h
      next hz =>
        dsimp [typeCount]
        split
        · contradiction
        · dsimp
          exact typeCount_TypeCount.mpr hz
  | .app a b => by
    constructor
    <;> intro h
    · dsimp [typeCount] at h
      obtain ⟨an, ap⟩ : ∃ n', typeCount t ls a = n' := exists_eq'
      obtain ⟨bn, bp⟩ : ∃ k', typeCount t ls b = k' := exists_eq'
      rw [ap, bp] at h
      rw [←h]
      exact .app (typeCount_TypeCount.mp ap) (typeCount_TypeCount.mp bp)
    · cases h
      next n k a b =>
      dsimp [typeCount]
      rw [(typeCount_TypeCount).mpr a, typeCount_TypeCount.mpr b]
  | .bvar id => by
    constructor
    <;> intro h
    · dsimp [typeCount] at h
      rw [←h]
      exact .bvar
    · cases h
      dsimp [typeCount]

inductive BvarArity : ℕ → Stx → ℕ → Prop
  | bvarEq  :                                       BvarArity i (.bvar i) 1
  | bvarNeq : i ≠ j                               → BvarArity i (.bvar j) 0
  | app     : BvarArity i a n → BvarArity i b k   → BvarArity i (.app a b) (n + k)
  | abs     : BvarArity i.succ body n             → BvarArity i (.abs _ body) n

def bvarArity (i : ℕ) : Stx → ℕ
  | .abs _ body => bvarArity i.succ body
  | .app a b => (bvarArity i a) + (bvarArity i b)
  | .bvar j => if i = j then 1 else 0

theorem bvarArity_BvarArity : bvarArity i s = n ↔ BvarArity i s n := match s with
  | .abs ty body => by
    constructor
    <;> intro h
    · dsimp [bvarArity] at h
      exact .abs (bvarArity_BvarArity.mp h)
    · dsimp [bvarArity]
      rcases h with (_|_|_|h)
      exact bvarArity_BvarArity.mpr h
  | .app a b => by
    constructor
    <;> intro h
    · dsimp [bvarArity] at h
      obtain ⟨an, ap⟩ : ∃ n', bvarArity i a = n' := exists_eq'
      obtain ⟨bn, bp⟩ : ∃ k', bvarArity i b = k' := exists_eq'
      rw [ap, bp] at h
      rw [←h]
      exact .app (bvarArity_BvarArity.mp ap) (bvarArity_BvarArity.mp bp)
    · dsimp [bvarArity]
      cases h
      next n' k' a b=>
      rw [←bvarArity_BvarArity.mpr a, ←bvarArity_BvarArity.mpr b]
  | .bvar j => by
    constructor
    <;> intro h
    · dsimp [bvarArity] at h
      split at h
      next hz =>
        rw [←h, hz]
        exact .bvarEq
      next hz =>
        rw [←h]
        exact .bvarNeq hz
    · rcases h with (_|h)
      <;> simp only [bvarArity, ite_eq_right_iff, one_ne_zero, imp_false, ↓reduceIte]
      exact h

end Counting

namespace Bounding1
/-
  max ((λ x. $0) $1) f =>
    let a := max $1 f
    max $0
-/

def ArgCount : Ty → Type
  | .arr a b  => ArgCount a → ArgCount b
  | .direct _ => ℕ

inductive TyArr : List Ty → Type
  | nil : TyArr []
  | cons (h : ArgCount hd) (t : TyArr tl) : TyArr (hd :: tl)

namespace TyArr

def get
    {idx : ℕ} (h : Γ[idx]? = some ty) (v : TyArr Γ)
    : ArgCount ty := match Γ, idx with
  | [], _ => Option.noConfusion (cast (by rw [List.getElem?_nil]) h)
  | hd :: tl, 0 =>
    let h := cast (by rw [List.getElem?_cons_zero, Option.some.injEq]) h
    match v with
    | .cons hd _ => cast (by rw [←h]) hd
  | hd :: tl, n+1 =>
    let h := cast (by rw [List.getElem?_cons_succ]) h
    match v with | cons _ tl' => get h tl'

end TyArr

namespace ArgCount

def inc (h : ArgCount v) : ArgCount v := match v with
  | .direct _ => Nat.succ h
  | .arr _ _ => fun a' => inc (h a')

theorem inferTyTransform
    (h : infer Γ (.app a b) = some rTy)
    (ha : infer Γ a = some aTy) (hb : infer Γ b = some bTy)
    : aTy = .arr bTy rTy := by
  simp only [infer, ha, hb, Option.bind_eq_bind, Option.some_bind] at h
  split at h
  <;> (try split at h)
  <;> (try contradiction)
  next h' =>
  rw [(Option.some.injEq _ _).mp h, h']

/--
  This is a function that extracts the type that's an argument to the application.
  This has to be done with a Σ' type over an ∃ because `Prop` can't be elim'd into `Type*`.
  That being said its output is exacly the same as if it was done with ∃.
-/
def inferExtract
    (h : infer Γ (.app a b) = some rTy)
    : (aTy : Ty) ×' (infer Γ a = (aTy ⇒ rTy) ∧ infer Γ b = aTy) :=
  match ha : infer Γ a, hb : infer Γ b with
  | some aTy, some bTy  =>
    ⟨_, Option.some_inj.mpr $ inferTyTransform h ha hb, rfl⟩
  | none, _ => by
    -- contra
    simp only [infer, ha, Option.bind_eq_bind, Option.none_bind] at h
  | some (.direct _), none
  | some (.arr _ _),  none => by
    simp only [infer, ha, hb, Option.bind_eq_bind, Option.none_bind, Option.some_bind] at h

set_option trace.split.failure true in
set_option pp.proofs true in
theorem inferExtract_def
    (h : infer Γ (.app a b) = some rTy)
    : ∃ aTy, ∃ p₁, ∃ p₂, inferExtract h = ⟨aTy, p₁, p₂⟩ := by
  rcases TySpec_app.mp (infer_TySpec.mp h) with ⟨argTy, p₁, p₂⟩
  have p₁ := infer_TySpec.mpr p₁
  have p₂ := infer_TySpec.mpr p₂
  use argTy
  use p₁
  use p₂
  dsimp [inferExtract]
  split
  /- · sorry -/
  /- · sorry -/
  /- · sorry -/
  /- · sorry -/

#print inferExtract

-- I finally see why proof-relevance is useful.
-- Damn that took me a long time to get
-- This does not work due to how AC is defined on Prop...
-- And (=) does only produce a Prop

theorem inferFwd : infer Γ (Stx.abs argTy body) = some (.arr argTy' retTy)
    → infer (argTy :: Γ) body = some retTy ∧ argTy = argTy' := by
  simp only [infer, Option.map_eq_some', Ty.arr.injEq, exists_eq_right_right, imp_self]

def upperBoundRed
    {x : Stx} (hTy : infer Γ x = some ty)
    (v : TyArr Γ)
    : ArgCount ty := match x, ty with
  | .bvar idx, _ => TyArr.get hTy v
  | .abs argTy body, .arr argTy' retTy =>
    let ⟨a, rfl⟩ := inferFwd hTy
    fun z => upperBoundRed a (.cons z v)
  | .abs argTy body, .direct _ => by
    -- contra
    simp only [infer, Option.map_eq_some', and_false, exists_false] at hTy
  | .app a b, _ =>
    let ⟨_, ha, hb⟩ := inferExtract hTy
    ArgCount.inc $ (upperBoundRed ha v) (upperBoundRed hb v)

def zero : ArgCount v := match v with
  | .direct _ => Nat.zero
  | .arr _ _ => fun _ => ArgCount.zero
def naturalize (h : ArgCount v) : ℕ := match v with
  | .direct _ => h
  | .arr _ _ => naturalize (h ArgCount.zero)

theorem naturalize_zero : naturalize (@zero v) = 0 := match v with
  | .direct _ => rfl
  | .arr _ _ => by dsimp [naturalize]; exact naturalize_zero

theorem naturalize_inc
    (x : ArgCount z)
    : (naturalize x) + 1 = naturalize (inc x) :=
  match z with
  | .direct _ => rfl
  | .arr _ _ => by simp only [naturalize, naturalize_inc, inc]

/- def lt (a b : ArgCount v) : Prop := match v with -/
/-   | .direct _ => Nat.lt a b -/
/-   | .arr arg _ => ∀ z : ArgCount arg, ArgCount.lt (a z) (b z) -/

/- theorem upperBoundRed_lt_inc -/
/-     {p : infer Γ x = some t} -/
/-     (h : upperBoundRed p Γ' = v) -/
/-     : ArgCount.lt v v.inc := match t with -/
/-     | .direct _ => by -/
/-       simp only [ArgCount.lt, ArgCount.inc, Nat.succ_eq_add_one, Nat.lt_eq, lt_add_iff_pos_right, -/
/-         zero_lt_one] -/
/-     | .arr a b => by -/
/-       intro z -/
/-       simp [ArgCount.lt, ArgCount.inc] -/
/-       sorry -/

end ArgCount

/- open ArgCount in -/
/- theorem z (h : infer Γ s = some v) : inferExtract p = ⟨_, _, _⟩ := sorry -/

open ArgCount in
theorem β_naturalize
    {p₁ : infer Γ (.app (.abs argTy body) arg) = some t₁}
    {p₂ : infer Γ (body.β arg) = some t₁}
    (h₁ : upperBoundRed p₁ Γ' = acA)
    (h₂ : upperBoundRed p₂ Γ' = acB)
    : naturalize acB < naturalize acA :=
  match body with
  | .abs argTy₂ b₂ => by
    obtain (_|(_|(_|_))) := infer_TySpec.mp p₁
    next p₁₁ p₁₂ =>
    cases p₁₂
    next p₁₂ =>
    let this := infer_TySpec.mpr p₁₂
    simp [upperBoundRed] at h₁
    simp [inferExtract] at h₁
    sorry
  | .bvar idx => by
    sorry
  | .app a b => sorry

end Bounding1


namespace Bounding2

-- C for constructive
inductive CTySpec : List Ty → Stx → Ty → Type
  | bvar ty : Γ[idx]? = some ty → CTySpec Γ (.bvar idx) ty

  | app argTy retTy : CTySpec Γ fn (argTy ⇒ retTy) → CTySpec Γ arg argTy
      → CTySpec Γ (.app fn arg) retTy
  | abs argTy retTy : CTySpec (argTy :: Γ) body retTy
      → CTySpec Γ (.abs ty body) (argTy ⇒ retTy)

def build (h : infer Γ s = some ty) : CTySpec Γ s ty :=
  match s with
  | .bvar idx => .bvar _ (by simpa only)
  | .abs ty body =>
    match h' : infer (ty :: Γ) body with
    | .none => by
      -- contra
      simp [infer, h'] at h
    | .some x => by
      simp only [infer, h', Option.map_some', Option.some.injEq] at h
      subst h
      exact .abs _ _ (build h')
  | .app a b =>
    have := Bounding1.inferExtract
    sorry

end Bounding2
