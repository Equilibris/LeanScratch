import LeanScratch.Semantics.L2.Stx
import Mathlib.Data.Rel
import Mathlib.Data.List.AList
import LeanScratch.Relation

namespace L2

abbrev VarMap := AList (fun _ : String => Int)

abbrev State := Expr × VarMap

inductive Red : State → State → Prop
  | op_add (a b : Int) : Red ⟨.op (.int a) .add (.int b), s⟩ ⟨.int (a + b), s⟩
  | op_gte (a b : Int) : Red ⟨.op (.int a) .gte (.int b), s⟩ ⟨.bool (a >= b), s⟩

  | op1 : Red ⟨e, s⟩ ⟨e', s'⟩
      → Red ⟨.op e o e2, s⟩ ⟨.op e' o e2, s'⟩
  | op2 : Red ⟨e2, s⟩ ⟨e2', s'⟩
      → e.isInt → Red ⟨.op e o e2, s⟩ ⟨.op e o e2', s'⟩

  | deref : (h : s.lookup addr = some x)
      → Red ⟨.deref (addr), s⟩ ⟨.int x, s⟩
  | assign1 : (h : ∃ x, s.lookup addr = some x)
      → Red ⟨.assign addr (.int v), s⟩ ⟨.skip, s.insert addr v⟩
  | assign2 : Red ⟨e, s⟩ ⟨e', s'⟩ → Red ⟨.assign addr e, s⟩ ⟨.assign addr e', s'⟩

  | seq1 : Red ⟨.seq .skip e, s⟩ ⟨e, s⟩
  | seq2 : Red ⟨e1, s⟩ ⟨e1', s'⟩
      → Red ⟨.seq e1 e2, s⟩ ⟨.seq e1' e2, s'⟩

  | if_t : Red ⟨.eif (.bool true) e1 e2, s⟩ ⟨e1, s⟩
  | if_f : Red ⟨.eif (.bool false) e1 e2, s⟩ ⟨e2, s⟩

  | if_cond : Red ⟨condition, s⟩ ⟨condition', s'⟩
      → Red ⟨.eif condition e1 e2, s⟩ ⟨.eif condition' e1 e2, s'⟩

  | ewhile : Red ⟨.ewhile c body, stx⟩ ⟨.eif c (.seq body (.ewhile c body)) .skip, stx⟩

  | beta : repl.isFnValue
      → Red ⟨.app (.abs name _ body) repl, s⟩ ⟨body.subst name repl, s⟩
  | app1 : Red ⟨e1, s⟩ ⟨e1', s'⟩
      → Red ⟨.app e1 e2, s⟩ ⟨.app e1' e2, s'⟩
  | app2 : e1.isFnValue → Red ⟨e2, s⟩ ⟨e2', s'⟩
      → Red ⟨.app e1 e2, s⟩ ⟨.app e1 e2', s'⟩

-- copy pasted from l1
@[simp]
theorem skip_op_int : Red ⟨.op (.skip) o e, s⟩ ⟨sta, stx⟩ → False := by
  intro h
  cases h
  <;> contradiction

@[simp]
theorem seq1_simp : Red ⟨.seq .skip e, s⟩ ⟨stx, sta⟩ → Red ⟨.seq .skip e, s⟩ ⟨e, s⟩ := fun _ => .seq1

@[simp]
theorem seq1_simp' : Red ⟨.seq .skip e, s⟩ ⟨stx, sta⟩ → stx = e ∧ s = sta := by
  intro h
  cases h
  · exact ⟨rfl, rfl⟩
  · contradiction

@[simp]
theorem if_t_simp : Red ⟨.eif (.bool true) e1 e2, s⟩ ⟨stx, sta⟩ → Red ⟨.eif (.bool true) e1 e2, s⟩ ⟨e1, s⟩ := fun _ => .if_t

@[simp]
theorem if_f_simp : Red ⟨.eif (.bool false) e1 e2, s⟩ ⟨stx, sta⟩ → Red ⟨.eif (.bool false) e1 e2, s⟩ ⟨e2, s⟩ := fun _ => .if_f

@[simp]
theorem assign_simp : Red ⟨.assign addr e, s⟩ ⟨stx, sta⟩ → (∃ e', ∃ s', Red ⟨e, s⟩ ⟨e', s'⟩ ∧ stx = .assign addr e' ∧ sta = s') ∨ (stx = .skip) := by
  intro h
  cases h
  · right
    rfl
  case assign2 e'2 a =>
    left
    use e'2
    use sta

@[simp]
theorem deref_simp : Red ⟨.deref addr, s⟩ ⟨stx, sta⟩ → (∃ i, stx = .int i) ∧ sta = s := by
  intro h
  cases h
  case deref x h =>
    constructor
    · use x
    · rfl

@[simp]
theorem skip_simp : Red ⟨.skip, s⟩ ⟨stx, sta⟩ ↔ False := by
  constructor
  <;> intro h
  · cases h
  · contradiction

@[simp]
theorem bool_simp : Red ⟨.bool b, s⟩ ⟨stx, sta⟩ ↔ False := by
  constructor
  <;> intro h
  · cases h
  · contradiction

@[simp]
theorem int_simp : Red ⟨.int b, s⟩ ⟨stx, sta⟩ ↔ False := by
  constructor
  <;> intro h
  · cases h
  · contradiction


@[simp]
theorem abs_simp : Red ⟨.abs nm ty body, s⟩ ⟨stx, sta⟩ ↔ False := by
  constructor
  <;> intro h
  · cases h
  · contradiction

@[simp]
theorem op_add_simp : Red ⟨.op (.int a) .add (.int b), s⟩ ⟨stx, sta⟩ → Red ⟨.op (.int a) .add (.int b), s⟩ ⟨.int (a + b), s⟩ := by
  intro h
  cases h <;> try trivial
  exact .op_add a b

@[simp]
theorem bool_op_int : Red ⟨.op (.bool b) o e, s⟩ ⟨sta, stx⟩ → False := by
  intro h
  cases h
  <;> contradiction

@[simp]
theorem op_elim : Red ⟨.op lhs o rhs, s⟩ ⟨post, s'⟩ → (
  if let .add := o then ∃ i, post = Expr.int i else ∃ b, post = Expr.bool b
) ∨ (∃ l, ∃ r, post = .op l o r) := by
  intro h
  cases h
  case op_add a b =>
    left
    use a + b
  case op_gte a b =>
    left
    simp only [ge_iff_le, Expr.bool.injEq, exists_const]
    use a >= b
  case op1 e' _ =>
    right
    use e'
    use rhs
  case op2 e2' _ _ =>
    right
    use lhs
    use e2'

theorem red_det : Red i o₁ ∧ Red i o₂ → o₁ = o₂ := by
  intro ⟨ha, hb⟩
  induction ha generalizing o₂
  <;> cases hb
  <;> try trivial

  case op1.op2 epre spre e₁ s₁ op eprealt ha a_ih e₂ s₂ epre_is_int hb => 
    have ⟨_, p⟩ := isInt_defn.mpr epre_is_int
    rw [p] at ha
    contradiction

  case op2.op1 epre spre e₁ s₁ e op ha e_is_int a_ih e₂ s₂ hb =>
    have ⟨_, p⟩ := isInt_defn.mpr e_is_int
    rw [p] at hb
    contradiction

  case op1.op1 epre spre e₁ s₁ o e2 ha a_ih e₂ s₂ hb =>
    injection a_ih hb with eq₁ eq₂
    rw [eq₁, eq₂]
  case op2.op2 epre spre e₁ s₁ _ op ha epre_is_int a_ih e₂ s₂ _ hb =>
    injection a_ih hb with eq₁ eq₂
    rw [eq₁, eq₂]

  case deref.deref h₁ _ h₂=>
    injection h₁.symm.trans h₂ with eq₁
    rw [eq₁]

  case assign2.assign2 epre spre e₁ s₁ addr ha a_ih e₂ s₂ hb =>
    injection a_ih hb with eq₁ eq₂
    rw [eq₁, eq₂]

  case seq2.seq2 epre spre e₁ s₁ erhs ha a_ih e₂ s₂ hb =>
    injection a_ih hb with eq₁ eq₂
    rw [eq₁, eq₂]

  case if_cond.if_cond condpre spre cond₁ s₁ e1 e2 ha a_ih cond₂ s₂ hb => 
    injection a_ih hb with eq₁ eq₂
    rw [eq₁, eq₂]

  case beta.app2 x name body repl s replVal _ _ _ a  =>
    cases repl
    <;> simp only at replVal
    <;> cases a
  case app1.app1 e s e₁ s₁ e₂ s₂ a_ih e₁' s₁' a =>
    injection a_ih a with eq₁ eq₂
    rw [eq₁, eq₂]
  case app1.app2 e _ _ _ _ a _ _ _ v _ =>
    cases e
    <;> simp only at v
    <;> cases a

  case app2.beta e _ _ _ a _ _ _ _ _ v =>
    cases e
    <;> simp only at v
    <;> cases a

  case app2.app1 e v _ _ _ _ a =>
    cases e
    <;> simp only at v
    <;> cases a
  case app2.app2 e s e₁ s₁ e' e'v _ a_ih _ _ _ a =>
    injection a_ih a with eq₁ eq₂
    rw [eq₁, eq₂]

end L2

