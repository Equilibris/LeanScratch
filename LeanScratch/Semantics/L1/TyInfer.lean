import LeanScratch.Semantics.L1.Stx
import LeanScratch.Semantics.L1.Red
import LeanScratch.Semantics.L1.Typed
import LeanScratch.Relation
import Batteries.Data.HashMap.Basic

def Ty.infer (ctx : Ctx) : Expr → Option Ty
  | .bool _ => some .bool
  | .int _  => some .int
  | .skip   => some .void

  | .op a op b => do
    let .int ← Ty.infer ctx a | none
    let .int ← Ty.infer ctx b | none
    match op with
    | .add => some .int
    | .gte => some .bool

  | .deref addr => do
    let _ ← ctx.lookup addr
    some .int
  | .assign addr e => do
    let .int ← Ty.infer ctx e | none
    let _ ← ctx.lookup addr
    some .void

  | .seq a b => do
    let .void ← Ty.infer ctx a | none
    Ty.infer ctx b

  | .eif c a b => do
    let .bool ← Ty.infer ctx c | none
    let a ← Ty.infer ctx a
    let b ← Ty.infer ctx b
    if a = b then some a
    else none

  | .ewhile c body => do
    let .bool ← Ty.infer ctx c    | none
    let .void ← Ty.infer ctx body | none
    some .void

section

def monize (f : α → β → γ) (h : α × β) : γ := let ⟨a, b⟩ := h; f a b
/- def demonize () -/
mutual
theorem TySpec_is_infer.eqMpNone {ctx : Ctx} {e : Expr} (ih : ∀ (ty : Ty), ¬TySpec ctx e ty) : Ty.infer ctx e = none := by
  induction e using Ty.infer.induct ctx
  next val =>
    exfalso
    exact ih .bool .bool
  next val =>
    exfalso
    exact ih .int .int
  next =>
    exfalso
    exact ih .void .skip
  next a op b a_ih b_ih =>
    by_cases ha : ∃ w, TySpec ctx a w
    · by_cases hb : ∃ w, TySpec ctx b w
      · rcases ha with ⟨wa, pa⟩
        rcases hb with ⟨wb, pb⟩

        simp only [Ty.infer, Option.bind_eq_bind, Option.bind_eq_none]
        intro ty ha
        obtain rfl := TyUnique ⟨pa, TySpec_is_infer.eqMprSome ha⟩

        cases wa
        <;> simp only [Option.bind_eq_none]

        intro ty hb
        obtain rfl := TyUnique ⟨pb, TySpec_is_infer.eqMprSome hb⟩
        cases wb
        <;> cases op
        <;> simp only
        <;> exfalso
        · exact ih .int  (.op_add pa pb)
        · exact ih .bool (.op_gte pa pb)

      · simp only [not_exists] at hb
        simp only [Ty.infer, b_ih hb, Option.bind_eq_bind, Option.none_bind, Option.bind_eq_none]
        intro ty _
        cases ty
        <;> simp only
    · simp only [not_exists] at ha
      simp only [Ty.infer, a_ih ha, Option.bind_eq_bind, Option.none_bind]
  next addr =>
    by_cases h : ∃ w, ctx.lookup addr = some w
    · exfalso
      exact ih .int (.deref h)
    · simp only [← Option.ne_none_iff_exists', ne_eq, Decidable.not_not] at h
      simp only [Ty.infer, h, Option.bind_eq_bind, Option.none_bind]
  next addr e e_ih =>
    by_cases h : ∃ w, TySpec ctx e w
    · rcases h with ⟨w, p⟩
      by_cases h : ∃ w, ctx.lookup addr = some w
      · simp only [Ty.infer, Option.bind_eq_bind, Option.bind_eq_none]
        intro ty h'
        obtain rfl := TyUnique ⟨p, TySpec_is_infer.eqMprSome h'⟩

        cases w
        <;> simp only [implies_true]
        exfalso
        exact ih .void (.assign h p)

      · simp only [← Option.ne_none_iff_exists', ne_eq, Decidable.not_not] at h
        simp only [Ty.infer, h, Option.bind_eq_bind, Option.none_bind, Option.bind_eq_none]
        intro ty
        cases ty
        <;> simp only [implies_true]

    · simp only [not_exists] at h
      simp only [Ty.infer, e_ih h, Option.bind_eq_bind, Option.none_bind]
  next a b a_ih b_ih =>
    by_cases ha : ∃ w, TySpec ctx a w
    · by_cases hb : ∃ w, TySpec ctx b w
      · simp only [Ty.infer, Option.bind_eq_bind, Option.bind_eq_none]
        rcases ha with ⟨wa, pa⟩
        rcases hb with ⟨wb, pb⟩
        intro ty ha
        obtain rfl := TyUnique ⟨pa, TySpec_is_infer.eqMprSome ha⟩
        cases wa
        <;> simp only
        exfalso
        exact ih wb (.seq pa pb)

      · simp only [not_exists] at hb
        simp only [Ty.infer, b_ih hb, Option.bind_eq_bind, Option.bind_eq_none]
        intro ty _
        cases ty
        <;> simp only

    · simp only [not_exists] at ha
      simp only [Ty.infer, a_ih ha, Option.bind_eq_bind, Option.none_bind]
  next c t f c_ih t_ih f_ih =>
    by_cases h₁ : ∃ w, TySpec ctx c w
    · by_cases h₂ : ∃ w, TySpec ctx t w
      · by_cases h₃ : ∃ w, TySpec ctx f w
        · simp only [Ty.infer, Option.bind_eq_bind, Option.bind_eq_none]
          rcases h₁ with ⟨w₁, p₁⟩
          rcases h₂ with ⟨w₂, p₂⟩
          rcases h₃ with ⟨w₃, p₃⟩
          intro ty h₁
          obtain rfl := TyUnique ⟨p₁, TySpec_is_infer.eqMprSome h₁⟩
          cases w₁
          <;> simp only [Option.bind_eq_none, ite_eq_right_iff, imp_false]
          intro ty h₂
          obtain rfl := TyUnique ⟨p₂, TySpec_is_infer.eqMprSome h₂⟩
          intro ty h₃
          obtain rfl := TyUnique ⟨p₃, TySpec_is_infer.eqMprSome h₃⟩
          by_contra!
          rw [this] at p₂
          exact ih w₃ (.eif p₁ p₂ p₃)

        · simp only [not_exists] at h₃
          simp only [Ty.infer, f_ih h₃, Option.bind_eq_bind, Option.none_bind, Option.bind_none,
            Option.bind_eq_none]
          intro ty _
          cases ty
          <;> simp only
      · simp only [not_exists] at h₂
        simp only [Ty.infer, t_ih h₂, Option.bind_eq_bind, Option.none_bind, Option.bind_eq_none]
        intro ty _
        cases ty
        <;> simp only
    · simp only [not_exists] at h₁
      simp only [Ty.infer, c_ih h₁, Option.bind_eq_bind, Option.none_bind]

  next c body c_ih body_ih =>
    by_cases h : ∃ w, TySpec ctx c w
    · rcases h with ⟨w, p⟩
      by_cases h : ∃ w, TySpec ctx body w
      · simp only [Ty.infer, Option.bind_eq_bind, Option.bind_eq_none]
        intro ty h'
        obtain rfl := TyUnique ⟨p, TySpec_is_infer.eqMprSome h'⟩
        cases w
        <;> simp only [Option.bind_eq_none]
        rcases h with ⟨w', p'⟩
        intro ty h'
        obtain rfl := TyUnique ⟨p', TySpec_is_infer.eqMprSome h'⟩
        cases w'
        <;> simp only

        exact ih .void (.ewhile p p')
      · simp only [not_exists] at h
        simp only [Ty.infer, body_ih h, Option.bind_eq_bind, Option.none_bind, Option.bind_eq_none]
        intro ty _
        cases ty
        <;> simp only

    · simp only [not_exists] at h
      simp only [Ty.infer, c_ih h, Option.bind_eq_bind, Option.none_bind]

theorem TySpec_is_infer.eqMprNone {ctx : Ctx} {e : Expr} (ih : Ty.infer ctx e = none) (ty : Ty) : ¬TySpec ctx e ty := by
  intro cont
  induction e generalizing ty
  <;> try { simp only [Ty.infer] at ih; done }
  <;> cases cont

  case op tya tyb =>
    simp only [Ty.infer, TySpec_is_infer.eqMpSome tya, TySpec_is_infer.eqMpSome tyb,
      Option.bind_eq_bind, Option.some_bind] at ih

  case op_gte tya tyb =>
    simp only [Ty.infer, TySpec_is_infer.eqMpSome tya, TySpec_is_infer.eqMpSome tyb,
      Option.bind_eq_bind, Option.some_bind] at ih

  case eif c t f =>
    simp only [Ty.infer, TySpec_is_infer.eqMpSome c, TySpec_is_infer.eqMpSome t,
      TySpec_is_infer.eqMpSome f, Option.bind_eq_bind, Option.some_bind, ↓reduceIte] at ih

  case ewhile c body =>
    simp only [Ty.infer, TySpec_is_infer.eqMpSome c, TySpec_is_infer.eqMpSome body,
      Option.bind_eq_bind, Option.some_bind] at ih
  case assign e _ h_addr ty =>
    rcases h_addr with ⟨w', p'⟩
    simp only [Ty.infer, TySpec_is_infer.eqMpSome ty, p', Option.bind_eq_bind, Option.some_bind]
      at ih

  case deref addr =>
    rcases addr with ⟨_, p⟩
    simp only [Ty.infer, p, Option.bind_eq_bind, Option.some_bind] at ih
  case seq tya tyb=>
    simp only [
      Ty.infer,
      TySpec_is_infer.eqMpSome tya,
      TySpec_is_infer.eqMpSome tyb,
      Option.bind_eq_bind,
      Option.some_bind
    ] at ih

theorem TySpec_is_infer.eqMpSome {ctx : Ctx} {e : Expr} {ty : Ty} (ih : TySpec ctx e ty) : Ty.infer ctx e = some ty := by
  induction ih
  <;> simp only [Ty.infer, Option.bind_eq_bind]
  <;> try simp_all only [Option.some_bind, ite_true]
  case deref h =>
    rcases h with ⟨_, p⟩
    simp only [p, Option.some_bind]
  case assign h _ _ =>
    rcases h with ⟨_, p⟩
    simp only [p, Option.some_bind]

theorem TySpec_is_infer.eqMprSome {ctx : Ctx} {e : Expr} {ty : Ty} (ih : Ty.infer ctx e = some ty) : TySpec ctx e ty := by
  induction e generalizing ty
  <;> simp only [Ty.infer, Option.bind_eq_bind, Option.some.injEq] at ih
  case bool =>
    rw [← ih]
    exact .bool
  case int =>
    rw [← ih]
    exact .int
  case skip =>
    rw [← ih]
    exact .skip
  case op lhs op rhs lhs_ih rhs_ih =>
    by_cases h : ∃ ty, Ty.infer ctx lhs = some ty
    <;> by_cases h' : ∃ ty, Ty.infer ctx rhs = some ty
    · rcases h  with ⟨w₁, p₁⟩
      rcases h' with ⟨w₂, p₂⟩
      cases w₁
      <;> cases w₂
      <;> simp only [p₁, p₂, Option.some_bind] at ih
      cases op
      <;> simp only [Option.some.injEq] at ih
      <;> rw [←ih]
      · exact .op_add (lhs_ih p₁) (rhs_ih p₂)
      · exact .op_gte (lhs_ih p₁) (rhs_ih p₂)
    · rcases h with ⟨w, h⟩
      simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h'
      cases w
      <;> simp only [h, h', Option.none_bind, Option.some_bind] at ih
    · rcases h' with ⟨w, h'⟩
      simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h
      cases w
      <;> simp only [h, h', Option.none_bind, Option.some_bind] at ih
    · simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at *
      simp only [h, h', Option.none_bind, Option.some_bind] at ih

  case eif cond t f cond_ih t_ih f_ih =>
    by_cases h : ∃ ty, Ty.infer ctx cond = some ty
    case neg =>
      simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h
      simp only [h, Option.none_bind, Option.some_bind] at ih

    rcases h with ⟨w, p⟩
    rw [p] at ih
    cases w
    <;> simp only [Option.some_bind] at ih

    by_cases h : ∃ ty, Ty.infer ctx t = some ty
    <;> by_cases h' : ∃ ty, Ty.infer ctx f = some ty
    · rcases h  with ⟨w₁, p₁⟩
      rcases h' with ⟨w₂, p₂⟩
      simp only [p₁, p₂, Option.some_bind, ite_some_none_eq_some] at ih
      rcases ih with ⟨w_eq, out⟩
      have : w₁ = w₂ := by cases w₁ <;> cases w₂ <;> trivial
      simp only [this] at *
      rw [← out]
      exact .eif (cond_ih p) (t_ih p₁) (f_ih p₂)

    · rcases h with ⟨w, h⟩
      simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h'
      cases w
      <;> simp only [h, h', Option.none_bind, Option.some_bind] at ih

    · rcases h' with ⟨w, h'⟩
      simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h
      cases w
      <;> simp only [h, h', Option.none_bind, Option.some_bind] at ih
    · simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at *
      simp only [h, h', Option.none_bind, Option.some_bind] at ih

  case ewhile cond e cond_ih e_ih => 
    by_cases h : ∃ ty, Ty.infer ctx cond = some ty
    <;> by_cases h' : ∃ ty, Ty.infer ctx e = some ty
    · rcases h  with ⟨w₁, p₁⟩
      rcases h' with ⟨w₂, p₂⟩
      cases w₁
      <;> cases w₂
      <;> simp only [p₁, p₂, Option.some_bind, Option.some.injEq] at ih
      rw [← ih]
      exact .ewhile (cond_ih p₁) (e_ih p₂)
    · rcases h with ⟨w, h⟩
      simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h'
      cases w
      <;> simp only [h, h', Option.none_bind, Option.some_bind] at ih
    · rcases h' with ⟨w, h'⟩
      simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h
      cases w
      <;> simp only [h, h', Option.none_bind, Option.some_bind] at ih
    · simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at *
      simp only [h, h', Option.none_bind, Option.some_bind] at ih

  case assign addr e e_ih =>
    by_cases h : ∃ ty, Ty.infer ctx e = some ty
    · rcases h with ⟨w, p⟩
      rw [p] at ih
      cases w
      <;> simp only [Option.some_bind] at ih
      by_cases h' : ∃ w, ctx.lookup addr = some w
      · rcases h' with ⟨w, h'⟩
        simp only [h', Option.some_bind, Option.some.injEq] at ih
        rw [← ih]
        exact .assign (Exists.intro w h') (e_ih p)

      · simp only [← Option.ne_none_iff_exists', ne_eq, Decidable.not_not] at h'
        simp only [h', Option.none_bind] at ih

    · simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h
      simp only [h, Option.none_bind, Option.some_bind] at ih
  case deref addr =>
    by_cases h : ∃ w, ctx.lookup addr = some w
    · rcases h with ⟨w, h⟩
      simp only [h, Option.some_bind, Option.some.injEq] at ih
      rw [← ih]
      exact .deref (Exists.intro w h)

    · simp only [← Option.ne_none_iff_exists', ne_eq, Decidable.not_not] at h
      simp only [h, Option.none_bind] at ih

  case seq a b a_ih b_ih =>
    by_cases h : ∃ ty, Ty.infer ctx a = some ty
    <;> by_cases h' : ∃ ty, Ty.infer ctx b = some ty
    · rcases h  with ⟨w₁, p₁⟩
      rcases h' with ⟨w₂, p₂⟩
      cases w₁
      <;> simp only [p₁, p₂, Option.some_bind, Option.some.injEq] at ih
      rw [← ih]
      exact .seq (a_ih p₁) (b_ih p₂)

    · rcases h with ⟨w, h⟩
      simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h'
      cases w
      <;> simp only [h, h', Option.none_bind, Option.some_bind] at ih

    · rcases h' with ⟨w, h'⟩
      simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h
      cases w
      <;> simp only [h, h', Option.none_bind, Option.some_bind] at ih

    · simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at *
      simp only [h, h', Option.none_bind, Option.some_bind] at ih
end

theorem TySpec_is_infer : Relation.optRel (monize TySpec) = Relation.graph (monize Ty.infer) := by
  apply funext₂
  intro ⟨ctx, e⟩ post
  apply propext

  constructor
  <;> intro ih
  <;> cases post
  <;> simp only [Relation.graph, Prod.exists, not_exists, Relation.optRel, monize] at *

  case mp.none =>
    exact TySpec_is_infer.eqMpNone ih
  case mpr.none =>
    exact TySpec_is_infer.eqMprNone ih
  case mp.some ty =>
    exact TySpec_is_infer.eqMpSome ih
  case mpr.some ty =>
    exact TySpec_is_infer.eqMprSome ih

/-- info: 'TySpec_is_infer' depends on axioms: [Quot.sound, propext, Classical.choice] -/
#guard_msgs in #print axioms TySpec_is_infer
end
