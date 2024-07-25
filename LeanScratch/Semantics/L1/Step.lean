import LeanScratch.Semantics.L1.Stx
import LeanScratch.Semantics.L1.Red
import Batteries.Data.HashMap.Basic
import Mathlib.Data.Rel
import LeanScratch.Relation

namespace L1

open Batteries (HashMap)

def step: State → Option State
  | ⟨.op a op b, s⟩ => match a, op, b with
    | .int a, .add, .int b => some ⟨.int (a + b), s⟩
    | .int a, .gte, .int b => some ⟨.bool (a >= b), s⟩
    | .int a, op, rhs => do
      let ⟨rhs, s⟩ ← step ⟨rhs, s⟩
      pure ⟨.op (.int a) op rhs, s⟩
    | lhs, op, rhs => do
      let ⟨lhs, s⟩ ← step ⟨lhs, s⟩
      pure ⟨.op lhs op rhs, s⟩
  | ⟨.deref h, s⟩ => (⟨.int ·, s⟩) <$> s.lookup h
  | ⟨.assign addr e, s⟩ => match e with
    | .int v => do
      let _ ← s.lookup addr
      some ⟨.skip, s.insert addr v⟩
    | e => do
      let ⟨e', s'⟩ ← step ⟨e, s⟩
      pure ⟨.assign addr e', s'⟩

  | ⟨.seq e₁ e₂, s⟩ => match e₁ with
    | .skip => some ⟨e₂, s⟩
    | e₁ => do
      let ⟨e₁, s'⟩ ← step ⟨e₁, s⟩
      pure ⟨.seq e₁ e₂, s'⟩

  | ⟨.eif condition e₁ e₂, s⟩ => match condition with
    | .bool true => some ⟨e₁, s⟩
    | .bool false => some ⟨e₂, s⟩
    | condition => do
      let ⟨condition, s⟩ ← step ⟨condition, s⟩
      pure ⟨.eif condition e₁ e₂, s⟩

  | ⟨.ewhile c body, s⟩ =>
      some ⟨.eif c (.seq body (.ewhile c body)) .skip, s⟩

  | _ => none

lemma step_skip_none : step ⟨.skip, s⟩ = none := by
  simp only [step, implies_true]
lemma step_bool_none : step ⟨.bool z, s⟩ = none := by
  simp only [step, implies_true]
lemma step_int_none : step ⟨.int z, s⟩ = none := by
  simp only [step, implies_true]

theorem x {γ : Sort _} {x : γ → Prop} : (∀ a, ¬(x a)) ↔ ¬∃ a, x a := by tauto

lemma forall_eq_none : (∀ a b, ¬(o = some (Prod.mk a b))) → (o = none) := by
  intro h
  exact Option.eq_none_iff_forall_not_mem.mpr fun a ↦ h a.1 a.2

set_option linter.unusedVariables false in
section
theorem red_is_step.eqMpNone {epre : Expr} {spre : VarMap}
    (ih : ∀ (e' : Expr) (s' : VarMap), ¬Red (epre, spre) (e', s')) : step (epre, spre) = none := by
  induction epre generalizing spre
  <;> try simp only [step]
  <;> try trivial
  case op lhs op rhs ih_lhs ih_rhs =>
    by_cases h : ∃ e' s', Red ⟨lhs, spre⟩ (e', s')
    · rcases h with ⟨e', s', p⟩
      exfalso
      exact ih (.op e' op rhs) s' (.op1 p)
    · simp only [not_exists] at h
      have ih_lhs := ih_lhs h
      by_cases h_rhs : ∃ e' s', Red ⟨rhs, spre⟩ (e', s')
      · rcases h_rhs with ⟨e', s', p⟩
        let lhsx := lhs
        cases lhs
        <;> try simp only [step, ih_lhs, Option.pure_def, Option.bind_eq_bind, Option.none_bind]
        exfalso
        refine ih (.op lhsx op e') s' (.op2 p ?_)
        simp only [Expr.isInt]

      · simp only [not_exists] at h_rhs
        have ih_rhs := ih_rhs h_rhs
        let lhsx := lhs
        cases lhs
        <;> try simp only [step, ih_lhs, Option.pure_def, Option.bind_eq_bind, Option.none_bind]
        next a _ =>
        let rhsx := rhs
        cases rhs
        <;> try simp only [step, ih_rhs, Option.pure_def, Option.bind_eq_bind, Option.none_bind]
        next b _ =>
        exfalso
        cases op
        · exact ih (.int  (a + b)) spre (.op_add a b)
        · exact ih (.bool (a ≥ b)) spre (.op_gte a b)

  case eif cond t f cond_ih _ _ => 
    by_cases h : ∃ e' s', Red ⟨cond, spre⟩ (e', s')
    · rcases h with ⟨e', s', p⟩
      exfalso
      exact ih (.eif e' t f) s' (.if_cond p)

    · simp only [not_exists] at h
      have cond_ih := cond_ih h
      cases cond
      <;> try simp only [step, cond_ih, Option.pure_def, Option.bind_eq_bind, Option.none_bind]
      next v _ =>
      cases v
      <;> exfalso
      · exact ih _ _ (.if_f)
      · exact ih _ _ (.if_t)
  case assign addr e e_ih =>
    by_cases h : ∃ e' s', Red ⟨e, spre⟩ (e', s')
    · rcases h with ⟨e', s', p⟩
      exfalso
      exact ih (.assign addr e') s' (.assign2 p)
    · simp only [not_exists] at h
      have e_ih := e_ih h
      cases e
      <;> simp only [step, e_ih, Option.pure_def, Option.bind_eq_bind, Option.none_bind]
      next val _ =>
      by_cases h : ∃ w, spre.lookup addr = some w
      · exfalso
        exact ih .skip _ (.assign1 h)
      · simp only [← Option.ne_none_iff_exists', ne_eq, Decidable.not_not] at h
        simp only [h, Option.none_bind]
  case deref addr =>
    by_cases h : ∃ w, spre.lookup addr = some w
    · rcases h with ⟨w, p⟩
      exfalso
      exact ih (.int w) spre (.deref p)
    · simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h
      simp only [h, Option.map_eq_map, Option.map_none']

  case seq a b ih_a _ =>
    by_cases h : ∃ e' s', Red ⟨a, spre⟩ (e', s')
    · rcases h with ⟨e', s', p⟩
      exfalso
      exact ih (.seq e' b) s' (.seq2 p)

    · simp only [not_exists] at h
      have ih_a := ih_a h
      cases a
      <;> simp only [step, ih_a, Option.pure_def, Option.bind_eq_bind, Option.none_bind]
      exact ih b spre (.seq1)
  case ewhile =>
    exact ih _ _ .ewhile

theorem red_is_step.eqMprNone {epre : Expr} {spre : VarMap} (ih : step (epre, spre) = none) (e' : Expr) :
  ∀ (s' : VarMap), ¬Red (epre, spre) (e', s') :=  by
  intro s' h
  induction epre generalizing e' s'
  <;> try trivial
  case op lhs op rhs lhs_ih rhs_ih =>
    unfold step at ih
    by_cases h' : ∃ w, step ⟨lhs, spre⟩ = some w
    · rcases h' with ⟨⟨eim, sim⟩, p⟩
      cases lhs
      <;> try {
        simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none, imp_false,
          Prod.forall] at ih
        exact ih eim sim p
      }
      · by_cases h' : ∃ w, step ⟨rhs, spre⟩ = some w
        · rcases h' with ⟨⟨e', s'⟩, p⟩
          cases rhs
          <;> try {
            simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none, imp_false,
              Prod.forall] at ih
            exact ih e' s' p
          }
          · cases op
            <;> simp only [ge_iff_le] at ih
        · simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h'
          cases h
          · simp only at ih
          · simp only [ge_iff_le] at ih
          · contradiction
          · simp only [step] at p
    · simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h'
      cases lhs
      /- <;> try contradiction -/
      <;> try {
        cases h
        · rename_i h
          exact lhs_ih h' _ _ h
        · contradiction
      }
      · cases h
        <;> simp only [ge_iff_le, Option.pure_def, Option.bind_eq_bind] at ih
        · contradiction
        · cases rhs
          <;> try simp only [Option.bind_eq_none, imp_false, Prod.forall] at ih
          <;> try {
            rename_i a
            exact rhs_ih (forall_eq_none ih) _ _ a
          }
          contradiction

  case eif cond _ _ cond_ih _ _ =>
    unfold step at ih
    cases h
    <;> try simp only [Option.pure_def, Option.bind_eq_bind] at ih
    case if_cond post_cond a =>
      let condx := cond
      cases cond
      <;> try {
        simp only at ih
        by_cases h : ∃ w, step ⟨condx, spre⟩ = some w
        · rcases h with ⟨w, p⟩
          rw [p] at ih
          simp only [Option.some_bind] at ih

        · simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h
          exact cond_ih h post_cond s' a
      }
      case bool val =>
        cases val
        <;> simp only at ih

  case assign addr e e_ih =>
    unfold step at ih
    simp at ih
    cases h
    case assign1 h =>
      rcases h with ⟨w, p⟩
      simp only [p, Option.some_bind] at ih
    case assign2 a =>
      cases e
      <;> simp only [Option.bind_eq_none, imp_false, Prod.forall] at ih
      <;> try exact e_ih (forall_eq_none ih) _ _ a
      contradiction
  case deref addr =>
    cases h
    case deref h =>
      simp only [step, h, Option.map_eq_map, Option.map_some'] at ih
  case seq a b a_ih _ =>
    let ax := a
    cases a
    <;> try {
      by_cases h' : ∃ w, step ⟨ax, spre⟩ = some w
      · rcases h' with ⟨w, p⟩
        simp only [step, p, Option.pure_def, Option.bind_eq_bind, Option.some_bind] at ih
      · simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h'
        unfold step at ih
        simp only [
          Option.pure_def,
          Option.bind_eq_bind,
          Option.bind_eq_none,
          imp_false,
          Prod.forall
        ] at ih
        cases h
        case neg.seq2 e1' a =>
          exact a_ih h' e1' s' a
    }
    case skip => 
      cases h
      · simp only [step] at ih
      · contradiction
  case ewhile => simp only [step] at ih

theorem red_is_step.eqMpSome {epre : Expr} {spre : VarMap} {post : State} (ih : Red (epre, spre) post) :
  step (epre, spre) = some post := by
  induction epre generalizing post
  <;> try trivial
  case op lhs op rhs lhs_ih rhs_ih =>
    unfold step
    cases ih
    · simp only [step]
    · simp only [step]
    case op1 e' s' a =>
      cases lhs
      <;> try {
        simp only [Option.pure_def, Option.bind_eq_bind]
        rw [lhs_ih a]
        simp only [Option.some_bind]
      }
      contradiction

    case op2 e2' s' lhs_is_int a =>
      have ⟨_, p⟩ := isInt_defn.mpr lhs_is_int
      cases lhs
      <;> cases rhs
      <;> try {
        simp only at p
        try contradiction
      }
      <;> simp only [Option.pure_def, Option.bind_eq_bind]
      <;> try {
        rw [rhs_ih a]
        simp only [Option.some_bind]
      }
      contradiction

  case assign adder e e_ih =>
    cases ih
    <;> try simp only [step]
    case assign2 e' s' ih =>
      cases e
      <;> unfold step
      <;> simp only [Option.pure_def, Option.bind_eq_bind]
      <;> try rw [e_ih ih]
      <;> simp only [Option.some_bind]
      contradiction
    case assign1 h =>
      rcases h with ⟨w, p⟩
      simp only [p, Option.bind_eq_bind, Option.some_bind]

  case eif cond t f cond_ih t_ih f_ih =>
    cases ih
    <;> try simp only [step]
    case if_cond cond' s' a =>
      cases cond
      <;> unfold step
      <;> simp only [Option.pure_def, Option.bind_eq_bind]
      <;> try rw [cond_ih a]
      <;> try simp only [Option.pure_def, Option.bind_eq_bind, Option.some_bind]
      contradiction
  case deref =>
    cases ih
    case deref x h =>
      simp only [step, h, Option.map_eq_map, Option.map_some']
  case seq a b a_ih b_ih =>
    cases ih
    · simp only [step]
    case seq2 e1' s h =>
      cases a
      <;> unfold step
      <;> simp only [Option.pure_def, Option.bind_eq_bind]
      <;> try rw [a_ih h]
      <;> simp only [Option.some_bind]
      contradiction
  case ewhile =>
    cases ih
    simp only [step]

theorem red_is_step.eqMprSome {epre : Expr} {spre : VarMap} {post : State} (ih : step (epre, spre) = some post) :
  Red (epre, spre) post := by
  induction epre generalizing post
  <;> try simp only [step, Option.map_eq_map, Option.map_eq_some'] at ih
  <;> try contradiction
  case op lhs op rhs lhs_ih rhs_ih =>
    by_cases h : ∃ w, step ⟨lhs, spre⟩ = some w
    · rcases h with ⟨⟨e', s'⟩, p⟩
      cases lhs
      <;> try {
        simp only [
          step,
          p,
          Option.pure_def,
          Option.bind_eq_bind,
          Option.some_bind,
          Option.some.injEq
        ] at ih
        rw [←ih]
        exact .op1 (lhs_ih p)
      }
      simp only [step] at p

    · simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h
      let lhsx := lhs
      cases lhs
      <;> try simp only [step, Option.pure_def, Option.bind_eq_bind, Option.none_bind, Option.map_eq_map, h] at ih
      case neg.int a =>
        by_cases h : ∃ w, step ⟨rhs, spre⟩ = some w
        case pos h' =>
          unfold step at ih
          cases rhs
          <;> simp only [
            step,
            Option.map_eq_map,
            Option.map_eq_some',
            Prod.exists,
            Prod.mk.injEq,
            exists_const,
            exists_false
          ] at h
          <;> rcases h with ⟨we, ws, p⟩
          <;> simp only [p, Option.pure_def, Option.bind_eq_bind, Option.some_bind, Option.some.injEq] at ih
          <;> try {
            rw [←ih]
            exact .op2 (rhs_ih p) (by simp only [Expr.isInt])
          }
          case ewhile.intro.intro => 
            simp only [step, Option.some_bind, Option.some.injEq] at ih
            rw [← ih]
            exact .op2 .ewhile (by simp only [Expr.isInt])

          · rcases p with ⟨w, find_eq, e_eq, s_eq⟩
            simp only [
              step,
              find_eq,
              Option.map_eq_map,
              Option.map_some',
              Option.some_bind,
              Option.some.injEq
            ] at ih
            rw [←ih]
            refine .op2 (rhs_ih ?x) (by simp only [Expr.isInt])
            simp only [
              step,
              Option.map_eq_map,
              Option.map_eq_some',
              Prod.mk.injEq,
              Expr.int.injEq,
              and_true,
              exists_eq_right
            ]
            exact find_eq

        · simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h
          cases rhs
          <;> try simp only [
            step,
            Option.pure_def,
            Option.bind_eq_bind,
            Option.none_bind,
            h
          ] at ih
          case neg.int b =>
            cases op
            <;> simp only [step, ge_iff_le, Option.some.injEq] at ih
            <;> rw [←ih]
            · exact .op_add a b
            · exact .op_gte a b

  case eif cond t f cond_ih _ _ =>
    by_cases h : ∃ o, step ⟨cond, spre⟩ = some o
    · rcases h with ⟨⟨e', s'⟩, p⟩
      cases cond
      <;> try {
        unfold step at ih
        simp only [p, Option.pure_def, Option.bind_eq_bind, Option.some_bind, Option.some.injEq] at ih
        rw [← ih]
        exact .if_cond (cond_ih p)
      }
      simp only [step, Option.map_eq_map, Option.map_eq_some', Prod.mk.injEq] at p
    · simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h
      cases cond
      <;> unfold step at ih
      <;> simp only [h, Option.pure_def, Option.bind_eq_bind, Option.none_bind] at ih
      case neg.bool v =>
        cases v
        <;> simp only [Option.some.injEq] at ih
        <;> rw [←ih]
        · exact .if_f
        · exact .if_t

  case assign addr e e_ih =>
    by_cases h : ∃ o, step ⟨e, spre⟩ = some o
    · rcases h with ⟨wa, p⟩
      cases e
      <;> simp only [
        step,
        Option.none_bind,
        Option.map_eq_map,
        Option.pure_def,
        Option.bind_eq_bind,
        Option.some.injEq
      ] at ih
      <;> try {
        simp only [p, Option.some_bind, Option.some.injEq] at ih
        rw [←ih]
        exact .assign2 (e_ih p)
      }
      case pos.intro.int =>
        by_cases h : ∃ z, spre.lookup addr = some z
        · let hx := h
          rcases h with ⟨_, p⟩
          simp only [p, Option.some_bind, Option.some.injEq] at ih
          rw [←ih]
          exact .assign1 hx
        · simp only [← Option.ne_none_iff_exists', ne_eq, Decidable.not_not] at h
          simp only [h, Option.none_bind] at ih
      case pos.intro.deref addr =>
        -- TODO: This is a very ugly proof
        by_cases h : ∃ v, spre.lookup addr = some v
        · rcases h with ⟨_, p'⟩
          simp only [p', Option.map_some', Option.some_bind, Option.some.injEq] at ih
          rw [←ih]
          refine .assign2 ?_
          rcases wa with ⟨e', s'⟩

          have px := p
          cases e'
          <;> simp only [step, Option.map_eq_map, Option.map_eq_some', Prod.mk.injEq, false_and, and_false, exists_const] at p
          rcases p with ⟨iw, ⟨find_iw, ieq, seq⟩⟩
          have x := find_iw.symm.trans p'
          injection x with eq₁
          rw [←eq₁]
          injection ieq with eq₂
          rw [←eq₂, ←seq] at px

          exact e_ih px

        · simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h
          simp only [h, Option.map_none', Option.none_bind] at ih
      case pos.intro.ewhile =>
        simp only [Option.some_bind, Option.some.injEq] at ih
        simp only [← ih]
        exact .assign2 .ewhile

    · simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h
      cases e
      <;> simp only [
        step,
        Option.none_bind,
        Option.map_eq_map,
        Option.pure_def,
        Option.bind_eq_bind,
        Option.some.injEq,
        h
      ] at ih
      by_cases h : ∃ z, spre.lookup addr = some z
      · let hx := h
        rcases h with ⟨_, p⟩
        simp only [p, Option.some_bind, Option.some.injEq] at ih
        rw [←ih]
        exact .assign1 hx
      · simp only [← Option.ne_none_iff_exists', ne_eq, Decidable.not_not] at h
        simp only [h, Option.none_bind] at ih

  case deref addr =>
    rcases ih with ⟨w, ⟨is_some, h⟩⟩
    rw [←h]
    exact .deref is_some

  case seq a b a_ih b_ih =>
    rcases post with ⟨epost, spost⟩
    unfold step at ih

    by_cases h : ∃ o, step ⟨a, spre⟩ = some o
    · rcases h with ⟨⟨e', s'⟩, p⟩
      cases a
      <;> simp only [Option.pure_def, Option.bind_eq_bind, Option.some.injEq, Prod.mk.injEq] at ih
      <;> try rw [p] at ih
      <;> simp only [Option.some_bind, Option.some.injEq, Prod.mk.injEq] at ih
      <;> rcases ih with ⟨iha, ihb⟩
      <;> rw [←iha, ←ihb]
      <;> have x := a_ih p
      <;> try exact .seq2 x
      simp only [step] at p
    · simp only [←Option.ne_none_iff_exists', ne_eq, not_not] at h
      cases a
      <;> simp only [
        h,
        Option.pure_def,
        Option.bind_eq_bind,
        Option.some.injEq,
        Prod.mk.injEq,
        Option.none_bind
      ] at ih
      rcases ih with ⟨rfl, rfl⟩
      exact .seq1
  case ewhile =>
    injection ih with eq
    rw [←eq]
    exact .ewhile

theorem red_is_step : Relation.optRel Red = Relation.graph step := by
  apply funext₂
  intro ⟨epre, spre⟩ post
  apply propext

  constructor
  <;> intro ih
  <;> cases post
  <;> simp only [Relation.graph, Prod.exists, not_exists, Relation.optRel] at *
  case mp.none =>
    exact red_is_step.eqMpNone ih
  case mpr.none =>
    exact red_is_step.eqMprNone ih

  case mp.some post =>
    exact red_is_step.eqMpSome ih

  case mpr.some post =>
    exact red_is_step.eqMprSome ih

/-- info: 'L1.red_is_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms red_is_step
end
end L1

