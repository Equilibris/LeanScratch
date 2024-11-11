import LeanScratch.Semantics.L1.Stx
import LeanScratch.Semantics.L1.Red
import LeanScratch.Relation
import Mathlib.Data.List.AList

namespace L1

inductive Ty
  | bool
  | int
  | void
deriving DecidableEq

-- TODO: Change Int to Unit
abbrev Ctx := AList fun _ : String => Int

inductive TySpec : Ctx → Expr → Ty → Prop
  | bool : TySpec _ (.bool b) .bool
  | int  : TySpec _ (.int i)  .int
  | skip : TySpec _ .skip     .void

  | op_add : TySpec ctx a .int → TySpec ctx b .int
      → TySpec ctx (.op a .add b) .int
  | op_gte : TySpec ctx a .int → TySpec ctx b .int
      → TySpec ctx (.op a .gte b) .bool

  | deref : (h : ∃ w, ctx.lookup addr = some w) 
      → TySpec ctx (.deref addr) .int
  | assign : (h : ∃ w, ctx.lookup addr = some w) → TySpec ctx e .int
      → TySpec ctx (.assign addr e) .void
  | seq : TySpec ctx a .void → TySpec ctx b o
      → TySpec ctx (.seq a b) o

  | eif : TySpec ctx c .bool → TySpec ctx t a → TySpec ctx f a
      → TySpec ctx (.eif c t f) a

  | ewhile : TySpec ctx c .bool → TySpec ctx body .void
      → TySpec ctx (.ewhile c body) .void

theorem TyUnique : TySpec ctx i o₁ ∧ TySpec ctx i o₂ → o₁ = o₂ := by
  rintro ⟨a, b⟩

  induction a generalizing o₂
  <;> cases b
  <;> try rfl
  case seq b_ih _ ba =>
    exact b_ih ba
  case eif t_ih _ _ ta _ =>
    exact t_ih ta

theorem AddrConsistency (trans : Red w₁ w₂) : (∃ w, w₁.snd.lookup addr = some w) → ∃ w, w₂.snd.lookup addr = some w := by
  intro h
  induction trans
  <;> simp_all only
  next addr' v _ _ =>
  by_cases h₂ : addr = addr'
  · use v
    simp [←h₂]
  · simp [←ne_eq] at h₂
    rcases h with ⟨w, p⟩
    use w
    simp only [AList.lookup_insert_ne h₂]
    exact p

theorem CtxConsistency (trans : Red ⟨e, s⟩ ⟨e', s'⟩) (a : TySpec s w x) : TySpec s' w x := by
  induction a
  · exact .bool
  · exact .int
  · exact .skip
  case op_add a b => exact .op_add a b
  case op_gte a b => exact .op_gte a b
  case deref h =>
    exact .deref (AddrConsistency trans h)
  case assign h _ deeper =>
    exact .assign (AddrConsistency trans h) deeper
  case seq a b => exact .seq a b
  case eif c t f => exact .eif c t f
  case ewhile c b => exact .ewhile c b

theorem TypePreservation : Red ⟨e, s⟩ ⟨e', s'⟩ → TySpec s e x → TySpec s' e' x := by
  intro h spec
  induction spec generalizing e' s'
  <;> cases h
  <;> try trivial
  · exact .int
  case op_add.op1 rhs lhs_ih _ _ a =>
    exact .op_add (lhs_ih a) (CtxConsistency a rhs)
  case op_add.op2 lhs _ _ rhs_ih _ _ a =>
    exact .op_add (CtxConsistency a lhs) (rhs_ih a)
  · exact .bool
  case op_gte.op1 rhs lhs_ih _ _ a =>
    exact .op_gte (lhs_ih a) (CtxConsistency a rhs)
  case op_gte.op2 lhs _ _ rhs_ih _ _ a =>
    exact .op_gte (CtxConsistency a lhs) (rhs_ih a)
  · exact .int
  · exact .skip
  case assign2 h _ a_ih _ a =>
    exact .assign (AddrConsistency a h) (a_ih a)
  case seq2 o a_ih _ _ a =>
    exact .seq (a_ih a) (CtxConsistency a o)
  case eif.if_cond t f c_ih _ _ _ a =>
    exact .eif (c_ih a) (CtxConsistency a t) (CtxConsistency a f)
  case ewhile c b _ _ =>
    exact .eif c (.seq b (.ewhile c b)) .skip

theorem Progress (spec : TySpec s e x) : (e.isValue ∨ ∃ w, Red ⟨e, s⟩ w) := by
  induction spec
  · left; simp only [Expr.isValue]
  · left; simp only [Expr.isValue]
  · left; simp only [Expr.isValue]
  case op_add a b ta tb a_ih b_ih =>
    right
    cases a_ih
    case inl h =>
      cases a
      <;> simp only [Expr.isValue] at h
      <;> cases ta
      next a =>
      cases b_ih
      case inl h =>
        cases b
        <;> simp only [Expr.isValue] at h
        <;> cases tb
        next b =>
        use ⟨.int (a + b), s⟩
        exact .op_add a b

      case inr h =>
        rcases h with ⟨⟨e', s'⟩, p⟩
        use ⟨.op (.int a) .add e', s'⟩
        exact .op2 p (by simp only [Expr.isInt])

    case inr h =>
      rcases h with ⟨⟨e', s'⟩, p⟩
      use ⟨e'.op .add b, s'⟩
      exact .op1 p
  case op_gte a b ta tb a_ih b_ih =>
    right
    cases a_ih
    case inl h =>
      cases a
      <;> simp only [Expr.isValue] at h
      <;> cases ta
      next a =>
      cases b_ih
      case inl h =>
        cases b
        <;> simp only [Expr.isValue] at h
        <;> cases tb
        next b =>
        use ⟨.bool (a ≥ b), s⟩
        exact .op_gte a b

      case inr h =>
        rcases h with ⟨⟨e', s'⟩, p⟩
        use ⟨.op (.int a) .gte e', s'⟩
        exact .op2 p (by simp only [Expr.isInt])

    case inr h =>
      rcases h with ⟨⟨e', s'⟩, p⟩
      use ⟨.op e' .gte b, s'⟩
      exact .op1 p

  case deref addr h =>
    right
    rcases h with ⟨w, p⟩
    use ⟨.int w, s⟩
    exact .deref p
  case assign e addr h ba_ih x =>
    right
    cases x
    case inl h =>
      cases e
      <;> simp only [Expr.isValue] at h
      <;> cases ba_ih
      next h' val =>
      use ⟨.skip, s.insert addr val⟩
      exact .assign1 h'
    case inr h =>
      rcases h with ⟨⟨e', s'⟩, p⟩
      use ⟨.assign addr e', s'⟩
      exact .assign2 p

  case seq ea eb _ a _ a_ih _ =>
    right
    cases a_ih
    case inl h =>
      use ⟨eb, s⟩
      rcases ea
      <;> simp only [Expr.isValue] at h
      <;> cases a
      exact .seq1

    case inr h =>
      rcases h with ⟨⟨e', s'⟩, p⟩
      use ⟨.seq e' eb, s'⟩
      exact .seq2 p
  case eif ec et _ ef c _ _ c_ih _ _ =>
    right
    cases c_ih
    case inl h =>
      cases ec
      <;> simp only [Expr.isValue] at h
      <;> cases c
      next val =>
      cases val
      · use ⟨ef, s⟩
        exact .if_f
      · use ⟨et, s⟩
        exact .if_t
    case inr h =>
      rcases h with ⟨⟨e', s'⟩ , p⟩
      use ⟨.eif e' et ef, s'⟩
      exact .if_cond p

  case ewhile c body _ _ _ _ =>
    right
    use ⟨.eif c (.seq body (.ewhile c body)) .skip, s⟩
    exact .ewhile

theorem LongTypePreservation (spec : TySpec s e ty) (h : RedStar ⟨e, s⟩ ⟨e', s'⟩) : TySpec s' e' ty := by
  have (w₁ w₂) (spec : TySpec w₁.snd w₁.fst ty) (h : RedStar w₁ w₂) : TySpec w₂.snd w₂.fst ty := by
    induction h
    case base base =>
      exact TypePreservation base spec
    case rfl => exact spec
    case trans l1_ih l2_ih =>
      exact l2_ih $ l1_ih spec
  have := this ⟨e, s⟩ ⟨e', s'⟩
  simp only at this
  exact this spec h

theorem Safety (spec : TySpec s e ty) (h : RedStar ⟨e, s⟩ ⟨e', s'⟩) : (e'.isValue ∨ ∃ w₃, Red ⟨e', s'⟩ w₃) := by
  cases h
  case base base =>
    exact Progress (TypePreservation base spec)
  case rfl => exact Progress spec
  case trans l1 l2 =>
    exact Progress $ (LongTypePreservation · l2) ∘ (LongTypePreservation · l1) $ spec

/-- info: 'L1.Safety' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Safety

end L1
