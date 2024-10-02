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

def concat : TyArr a → TyArr b → TyArr (a ++ b)
  | .nil, a => a
  | .cons hd tl, v => .cons hd (concat tl v)

instance : HAppend (TyArr a) (TyArr b) (TyArr (a ++ b)) := ⟨TyArr.concat⟩
theorem cons_append {a : TyArr A} {b : TyArr B} : .cons z (a ++ b) = (TyArr.cons z a) ++ b := rfl

@[simp]
theorem nil_concat {Γ' : TyArr Γ} : (TyArr.nil ++ Γ') = Γ' := rfl

def get
    {idx : ℕ} (h : Γ[idx]? = some ty) (v : TyArr Γ)
    : ArgCount ty := match Γ, idx with
  | [], _ => Option.noConfusion (List.getElem?_nil.symm.trans h)
  | hd :: tl, 0 =>
    let h := (Option.some.injEq _ _).mp $ List.getElem?_cons_zero.symm.trans h
    match v with
    | .cons hd _ => cast (by rw [←h]) hd
  | hd :: tl, n+1 =>
    match v with
    | cons _ tl' => get (List.getElem?_cons_succ.symm.trans h) tl'

theorem get_append_assoc
    {Γ₁' : TyArr Γ₁} {Γ₂' : TyArr Γ₂} {Γ₃' : TyArr Γ₃}
    {h  : (Γ₁ ++  Γ₂ ++ Γ₃ )[idx]? = some v}
    (h' : (Γ₁ ++ (Γ₂ ++ Γ₃))[idx]? = some v)
    : get h (Γ₁' ++  Γ₂' ++ Γ₃') = get h' (Γ₁' ++ (Γ₂' ++ Γ₃')) :=
  match Γ₁, Γ₁', idx with
  | [], .nil, _ => rfl
  | hd :: tl, .cons hd' tl', 0 => by
    change get h (cons hd' (tl' ++ Γ₂' ++ Γ₃')) = get h' (cons hd' (tl' ++ (Γ₂' ++ Γ₃')))
    dsimp [get]
  | hd :: tl, .cons hd' tl', n+1 => by
    change get h (cons hd' (tl' ++ Γ₂' ++ Γ₃')) = get h' (cons hd' (tl' ++ (Γ₂' ++ Γ₃')))
    dsimp [get]
    exact get_append_assoc _

theorem get_append
    {Γ₁' : TyArr Γ₁} {Γ₂' : TyArr Γ₂}
    {h  : (Γ₁ ++ Γ₂)[idx]? = some t}
    (h' :         Γ₁[idx]? = some t)
    : get h (Γ₁' ++ Γ₂') = get h' Γ₁' :=
  match Γ₁, Γ₁', idx with
  | [], _, _ => (Nat.not_succ_le_zero _ (List.getElem?_lt_length h')).elim
  | hd :: tl, .cons hd' tl', 0 => by
    change (hd :: (tl ++ Γ₂))[0]? = _ at h
    change get _ (TyArr.cons hd' (tl' ++ Γ₂')) = _
    dsimp [get]
  | hd :: tl, .cons hd' tl', n+1 => by
    change (hd :: (tl ++ Γ₂))[n + 1]? = _ at h
    change get _ (TyArr.cons hd' (tl' ++ Γ₂')) = _
    dsimp [get]
    exact get_append _

theorem get_idx_eq_jdx
    {idx jdx : ℕ}
    {Γ' : TyArr Γ}
    {h  : Γ[idx]? = some t}
    (h' : Γ[jdx]? = some t)
    (heq : idx = jdx)
    : get h Γ' = get h' Γ' :=
  match Γ, Γ', idx, jdx with
  | [], .nil, _, _ => Option.noConfusion (List.getElem?_nil.symm.trans h)
  | hd :: tl, .cons hd' tl', 0, 0 => rfl
  | hd :: tl, .cons hd' tl', idx+1, jdx+1 => by
    dsimp [get]
    simp only [add_left_inj] at heq
    exact get_idx_eq_jdx _ heq

set_option pp.proofs true in
theorem get_append_right
    {Γ₁' : TyArr Γ₁} {Γ₂' : TyArr Γ₂}
    {h  : (Γ₁ ++ Γ₂)[idx]? = some t}
    (hLe : Γ₁.length ≤ idx)
    (h' :  Γ₂[idx - Γ₁.length]? = some t)
    : get h (Γ₁' ++ Γ₂') = get h' Γ₂' :=
  match Γ₁, Γ₁', idx with
  | [], .nil, idx => by
    change get _ Γ₂' = _
    dsimp [List.length_nil, Nat.sub_zero] at h h'
    rfl
  | hd :: tl, .cons hd' tl', 0 => by
    simp only [nonpos_iff_eq_zero, List.length_eq_zero, one_ne_zero] at hLe
  /- | hd :: tl, .cons hd' tl', [], .nil,  n+1 => by -/
  /-   simp only [List.length_cons, Nat.reduceSubDiff, List.getElem?_nil] at h' -/
  | hd :: tl, .cons hd' tl', n+1 => by
    change (hd :: (tl ++ _))[n + 1]? = _ at h
    change get _ (TyArr.cons hd' (tl' ++ Γ₂')) = _
    dsimp [get]
    simp only [List.length_cons, add_le_add_iff_right] at hLe
    dsimp at h'
    have : (n + 1 - (tl.length + 1)) = (n - tl.length) := Nat.add_sub_add_right n 1 tl.length
    rw [this] at h'
    rw [get_idx_eq_jdx h' this]
    exact get_append_right hLe _

end TyArr

-- I finally see why proof-relevance is useful.
-- Damn that took me a long time to get
-- This does not work due to how AC is defined on Prop...
-- And (=) does only produce a Prop

-- C for constructive
inductive CTySpec : List Ty → Stx → Ty → Type
  | bvar : Γ[idx]? = some ty → CTySpec Γ (.bvar idx) ty

  | app : CTySpec Γ fn (argTy ⇒ retTy) → CTySpec Γ arg argTy
      → CTySpec Γ (.app fn arg) retTy
  | abs : CTySpec (argTy :: Γ) body retTy
      → CTySpec Γ (.abs argTy body) (argTy ⇒ retTy)

theorem CTySpec_TySpec (h : CTySpec Γ s ty) : TySpec Γ s ty := by
  induction h
  · exact .bvar (by assumption)
  · exact .app (by assumption) (by assumption)
  · exact .abs (by assumption)

def build (h : infer Γ s = some ty) : CTySpec Γ s ty :=
  match s with
  | .bvar idx => .bvar (by simpa only)
  | .abs ty body =>
    match h' : infer (ty :: Γ) body with
    | .none => by
      -- contra
      simp [infer, h'] at h
    | .some x => by
      simp only [infer, h', Option.map_some', Option.some.injEq] at h
      subst h
      exact .abs (build h')
  | .app a b =>
    match ha : infer Γ a, hb : infer Γ b with
    | some aTy, some bTy => by
      simp only [infer, ha, hb, Option.bind_eq_bind, Option.some_bind] at h
      split at h
      <;> (try split at h)
      <;> (try contradiction)
      next h' =>
      have := ((Option.some.injEq _ _).mp h)
      subst this h'
      exact .app (build ha) (build hb)
    | none, _ => by
      -- contra
      simp only [infer, ha, Option.bind_eq_bind, Option.none_bind] at h
    | some (.direct _), none
    | some (.arr _ _),  none => by
      simp only [infer, ha, hb, Option.bind_eq_bind, Option.none_bind, Option.some_bind] at h

def TySpec_CTySpec (h : TySpec Γ s ty) : CTySpec Γ s ty := build (infer_TySpec.mpr h)

theorem CTySpec_unique (h₁ : CTySpec Γ s o₁) (h₂ : CTySpec Γ s o₂) : o₁ = o₂ :=
  TySpec_unique (CTySpec_TySpec h₁) (CTySpec_TySpec h₂)

namespace ArgCount

def inc (h : ArgCount v) : ArgCount v := match v with
  | .direct _ => Nat.succ h
  | .arr _ _ => fun a' => inc (h a')

def addN (h : ArgCount v) (n : ℕ) : ArgCount v := match v with
  | .direct _ => Nat.add h n
  | .arr _ _ => fun a' => addN (h a') n

theorem addN_succ_inc {v : ArgCount t} : addN v (n + 1) = inc (addN v n) :=
  match t with
  | .direct _ => rfl
  | .arr a b => by
    dsimp [addN, inc]
    apply funext
    intro v
    rw [addN_succ_inc]
theorem addN_zero {v : ArgCount t} : addN v 0 = v :=
  match t with
  | .direct _ => rfl
  | .arr _ _ => by
    dsimp [addN, inc]
    apply funext
    intro x
    rw [addN_zero]

def zero : ArgCount v := match v with
  | .direct _ => Nat.zero
  | .arr _ _ => fun _ => ArgCount.zero
def naturalize (h : ArgCount v) : ℕ := match v with
  | .direct _ => h
  | .arr _ _ => naturalize (h ArgCount.zero)

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

@[simp]
theorem naturalize_zero : naturalize (@zero v) = 0 := match v with
  | .direct _ => rfl
  | .arr _ _ => by dsimp [naturalize]; exact naturalize_zero

@[simp]
theorem naturalize_inc
    (x : ArgCount z)
    : (naturalize x) + 1 = naturalize (inc x) :=
  match z with
  | .direct _ => rfl
  | .arr _ _ => by dsimp [naturalize, inc]; rw [naturalize_inc]

@[simp]
theorem naturalize_addN {a : ArgCount ty} : (addN a n).naturalize = a.naturalize + n :=
  match ty with
  | .direct _ => rfl
  | .arr a b => by
    dsimp [addN, naturalize]
    rw [naturalize_addN]

end ArgCount

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
      dsimp
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
theorem β_naturalize
    {p₁ : CTySpec Γ (.app (.abs argTy body) arg) t₁}
    {p₂ : CTySpec Γ (body.β arg) t₁}
    (h₁ : upperBoundRed p₁ Γ' = acA)
    (h₂ : upperBoundRed p₂ Γ' = acB)
    : naturalize acB < naturalize acA := by
  dsimp [Stx.β] at p₂
  cases p₁; next pRepl hBody =>
  cases hBody; next hBody =>
  cases h₁
  dsimp [upperBoundRed]
  change CTySpec ([] ++ Γ) _ _ at pRepl
  change CTySpec ([] ++ (_ :: Γ)) _ _ at hBody
  obtain ⟨replSz, z⟩ : ∃ replSz, upperBoundRed pRepl Γ' = replSz := exists_eq'
  have x := upperBoundRed_eq_replace (Γ₂ := []) (Γ'₂ := .nil) pRepl z hBody p₂
  change upperBoundRed _ (TyArr.cons _ _) = _ at x
  rw [z, x, ←h₂, naturalize_addN, Nat.add_comm (m := 1), ←Nat.add_assoc]
  change _ < (upperBoundRed _ Γ').naturalize + 1 + _
  calc
    _ < _ + 1 := Nat.lt_succ_self _
    _ ≤ _ := Nat.le_add_right ((upperBoundRed p₂ Γ').naturalize + 1) replSz.naturalize

/-- info: 'STLC.β_naturalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms β_naturalize

