import LeanScratch.Semantics.L1.Stx
import LeanScratch.Semantics.L1.Red
import LeanScratch.Semantics.L1.Typed
import LeanScratch.Semantics.L1.Step

namespace L1

section Q1
def factorial : Expr := [l1|
  while !l2 do (
    (l3 := !l2);
    (l4 := !l1);
    (while !l3 ≥ 2 do
      ((l1 := !l1 + !l4);
       (l3 := !l3 + -1)));
    l2 := !l2 + -1
  )]

/--
info: def L1.factorial : Expr :=
(Expr.deref "l2").ewhile
  ((Expr.assign "l3" (Expr.deref "l2")).seq
    ((Expr.assign "l4" (Expr.deref "l1")).seq
      ((((Expr.deref "l3").op Op.gte (Expr.int 2)).ewhile
            ((Expr.assign "l1" ((Expr.deref "l1").op Op.add (Expr.deref "l4"))).seq
              (Expr.assign "l3" ((Expr.deref "l3").op Op.add (Expr.int (-1)))))).seq
        (Expr.assign "l2" ((Expr.deref "l2").op Op.add (Expr.int (-1)))))))
-/
#guard_msgs in
#print factorial
end Q1

section Q2

abbrev initQ2 := (∅ : VarMap).insert "l0" 0 |>.insert "l1" 0

example
    : Relation.ReflTransGen Red
      ⟨[l1| (l0 := 7); (l1 := !l0 + 2)], initQ2⟩
      (Expr.skip, AList.insert "l1" ((Int.ofNat 7) + 2) (AList.insert "l0" 7 initQ2))
    :=
  (.tail
    (.tail
      (.tail
        (.tail
          (.tail
            .refl
            $ .seq2
            $ .assign1 (⟨0, rfl⟩))
          .seq1)
        $ .assign2 (.op1 (.deref (by reduce; rfl))))
    $ .assign2 $ .op_add _ _)
    $ .assign1 ⟨0, by reduce; rfl⟩)

end Q2

section Q3

abbrev initQ3 := (∅ : VarMap).insert "l1" 3 |>.insert "l2" 0

/- abbrev prog : Expr :=  -/

example
    : Relation.ReflTransGen Red
      ⟨ [l1|
        (l2 := 0);
        while !l1 ≥ 1 do (
          (l2 := !l2 + !l1);
          (l1 := !l1 + -1)
        )], initQ3⟩
      -- Sorry ugly type, I cannot be bothered to type this in the new syntax form
      -- Can also be solved by unification but lean bans this in top-level decls
      (((Expr.int (Int.ofNat 3)).op Op.gte (Expr.int 1)).eif
        (((Expr.assign "l2" ((Expr.deref "l2").op Op.add (Expr.deref "l1"))).seq
              (Expr.assign "l1" ((Expr.deref "l1").op Op.add (Expr.int (-1))))).seq
          (((Expr.deref "l1").op Op.gte (Expr.int 1)).ewhile
            ((Expr.assign "l2" ((Expr.deref "l2").op Op.add (Expr.deref "l1"))).seq
              (Expr.assign "l1" ((Expr.deref "l1").op Op.add (Expr.int (-1)))))))
        Expr.skip,
       AList.insert "l2" 0 initQ3)
    :=
  (.tail
    (.tail
      (.tail
        (.tail
          .refl
          $ .seq2 $ .assign1 ⟨0, (by reduce; rfl)⟩)
        .seq1)
      .ewhile)
    $ .if_cond $ .op1 $ .deref (by reduce; rfl))

end Q3

section Q8

abbrev Γ := (∅ : VarMap).insert "l1" 0 |>.insert "l2" 0 |>.insert "l3" 0

example : TySpec Γ [l1|
    (l2 := 0);
    while !l1 ≥ 1 do (
      (l2 := !l2 + !l1);
      (l1 := !l1 + -1)
    )] .void :=
  .seq
    (.assign ⟨0, rfl⟩ .int)
    (.ewhile
      (.op_gte
        (.deref ⟨0, rfl⟩)
        .int)
      (.seq
        (.assign ⟨0, rfl⟩
          (.op_add
            (.deref ⟨0, rfl⟩)
            (.deref ⟨0, rfl⟩)))
        (.assign ⟨0, rfl⟩
          (.op_add
            (.deref ⟨0, rfl⟩)
            .int))))

end Q8

section Q9

inductive Red' : State → State → Prop
  | op_add (a b : Int) : Red' ⟨.op (.int a) .add (.int b), s⟩ ⟨.int (a + b), s⟩
  | op_gte (a b : Int) : Red' ⟨.op (.int a) .gte (.int b), s⟩ ⟨.bool (a >= b), s⟩

  | op1 : Red' ⟨e, s⟩ ⟨e', s'⟩
      → Red' ⟨.op e o e2, s⟩ ⟨.op e' o e2, s'⟩
  | op2 : Red' ⟨e2, s⟩ ⟨e2', s'⟩
      → e.isInt → Red' ⟨.op e o e2, s⟩ ⟨.op e o e2', s'⟩

  | deref : (h : s.lookup addr = some x)
      → Red' ⟨.deref (addr), s⟩ ⟨.int x, s⟩

  -- added in this case
  | assign1' : (h : ∃ x, s.lookup addr = some x)
      → Red' ⟨.assign addr (.int v), s⟩ ⟨.int v, s.insert addr v⟩
  | assign2 : Red' ⟨e, s⟩ ⟨e', s'⟩ → Red' ⟨.assign addr e, s⟩ ⟨.assign addr e', s'⟩

  -- added in this case
  | seq1' : v.isValue = .true → Red' ⟨.seq v e, s⟩ ⟨e, s⟩
  | seq2  : Red' ⟨e1, s⟩ ⟨e1', s'⟩
      → Red' ⟨.seq e1 e2, s⟩ ⟨.seq e1' e2, s'⟩

  | if_t: Red' ⟨.eif (.bool true) e1 e2, s⟩ ⟨e1, s⟩
  | if_f: Red' ⟨.eif (.bool false) e1 e2, s⟩ ⟨e2, s⟩

  | if_cond: Red' ⟨condition, s⟩ ⟨condition', s'⟩
      → Red' ⟨.eif condition e1 e2, s⟩ ⟨.eif condition' e1 e2, s'⟩

  | ewhile : Red' ⟨.ewhile c body, stx⟩ ⟨.eif c (.seq body (.ewhile c body)) .skip, stx⟩

def TypePres (r : State → State → Prop) : Prop := ∀ {e s e' s'}, r ⟨e, s⟩ ⟨e', s'⟩ → ∃ t, TySpec s e t ∧ TySpec s' e' t

example : ¬TypePres Red' := fun x => by
  -- construct counter example
  have : Red' ⟨[l1|l1 := 0], (∅ : VarMap).insert "l1" 0⟩ ⟨[l1|0], ((∅ : VarMap).insert "l1" 0).insert "l1" 0⟩ := .assign1' ⟨0, rfl⟩
  rcases x this with ⟨w, hpre, hpost⟩
  -- show that w must equal .int
  obtain rfl := TyUnique ⟨.assign ⟨0, by rfl⟩ .int, hpre⟩
  -- cases hpre -- Alternative proof, simply remove the use of TyUnique
  -- cases hpost
  exact Ty.noConfusion $ TyUnique ⟨.int, hpost⟩

end Q9

section Q10

inductive TySpec' : Ctx → Expr → Ty → Prop
  | bool : TySpec' _ (.bool b) .bool
  | int  : TySpec' _ (.int i)  .int
  | skip : TySpec' _ .skip     .void

  | op_add : TySpec' ctx a .int → TySpec' ctx b .int
      → TySpec' ctx (.op a .add b) .int
  | op_gte : TySpec' ctx a .int → TySpec' ctx b .int
      → TySpec' ctx (.op a .gte b) .bool

  | deref : (h : ∃ w, ctx.lookup addr = some w) 
      → TySpec' ctx (.deref addr) .int
  -- We change this type
  | assign : (h : ∃ w, ctx.lookup addr = some w) → TySpec' ctx e .int
      → TySpec' ctx (.assign addr e) .int
  | seq : TySpec' ctx a .void → TySpec' ctx b o
      → TySpec' ctx (.seq a b) o

  | eif : TySpec' ctx c .bool → TySpec' ctx t a → TySpec' ctx f a
      → TySpec' ctx (.eif c t f) a

  | ewhile : TySpec' ctx c .bool → TySpec' ctx body .void
      → TySpec' ctx (.ewhile c body) .void

-- Below is a proof of type-consistency for TySpec' and Red'

theorem AddrConsistency' (trans : Red' w₁ w₂) : (∃ w, w₁.snd.lookup addr = some w) → ∃ w, w₂.snd.lookup addr = some w := by
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

theorem CtxConsistency' (trans : Red' ⟨e, s⟩ ⟨e', s'⟩) (a : TySpec' s w x) : TySpec' s' w x := by
  induction a
  · exact .bool
  · exact .int
  · exact .skip
  case op_add a b => exact .op_add a b
  case op_gte a b => exact .op_gte a b
  case deref h =>
    exact .deref (AddrConsistency' trans h)
  case assign h _ deeper =>
    exact .assign (AddrConsistency' trans h) deeper
  case seq a b => exact .seq a b
  case eif c t f => exact .eif c t f
  case ewhile c b => exact .ewhile c b

theorem TypePreservation' : Red' ⟨e, s⟩ ⟨e', s'⟩ → TySpec' s e x → TySpec' s' e' x := by
  intro h spec
  induction spec generalizing e' s'
  <;> cases h
  <;> try trivial
  · exact .int
  case op_add.op1 rhs lhs_ih _ _ a =>
    exact .op_add (lhs_ih a) (CtxConsistency' a rhs)
  case op_add.op2 lhs _ _ rhs_ih _ _ a =>
    exact .op_add (CtxConsistency' a lhs) (rhs_ih a)
  · exact .bool
  case op_gte.op1 rhs lhs_ih _ _ a =>
    exact .op_gte (lhs_ih a) (CtxConsistency' a rhs)
  case op_gte.op2 lhs _ _ rhs_ih _ _ a =>
    exact .op_gte (CtxConsistency' a lhs) (rhs_ih a)
  · exact .int
  · exact .int
  case assign2 h _ a_ih _ a =>
    exact .assign (AddrConsistency' a h) (a_ih a)
  case seq2 o a_ih _ _ a =>
    exact .seq (a_ih a) (CtxConsistency' a o)
  case eif.if_cond t f c_ih _ _ _ a =>
    exact .eif (c_ih a) (CtxConsistency' a t) (CtxConsistency' a f)
  case ewhile c b _ _ =>
    exact .eif c (.seq b (.ewhile c b)) .skip

/-- info: 'L1.TypePreservation'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms TypePreservation'

end Q10

section Q13

inductive RedND : State → State → Prop
  | op_add (a b : Int) : RedND ⟨.op (.int a) .add (.int b), s⟩ ⟨.int (a + b), s⟩
  | op_gte (a b : Int) : RedND ⟨.op (.int a) .gte (.int b), s⟩ ⟨.bool (a >= b), s⟩

  | op1  : RedND ⟨e, s⟩ ⟨e', s'⟩
      → RedND ⟨.op e o e2, s⟩ ⟨.op e' o e2, s'⟩
  | op1b : RedND ⟨e2, s⟩ ⟨e2', s'⟩
      → RedND ⟨.op e o e2, s⟩ ⟨.op e o e2', s'⟩

  | deref : (h : s.lookup addr = some x)
      → RedND ⟨.deref (addr), s⟩ ⟨.int x, s⟩
  | assign1 : (h : ∃ x, s.lookup addr = some x)
      → RedND ⟨.assign addr (.int v), s⟩ ⟨.skip, s.insert addr v⟩
  | assign2 : RedND ⟨e, s⟩ ⟨e', s'⟩ → RedND ⟨.assign addr e, s⟩ ⟨.assign addr e', s'⟩

  | seq1: RedND ⟨.seq .skip e, s⟩ ⟨e, s⟩
  | seq2: RedND ⟨e1, s⟩ ⟨e1', s'⟩
      → RedND ⟨.seq e1 e2, s⟩ ⟨.seq e1' e2, s'⟩

  | if_t: RedND ⟨.eif (.bool true) e1 e2, s⟩ ⟨e1, s⟩
  | if_f: RedND ⟨.eif (.bool false) e1 e2, s⟩ ⟨e2, s⟩

  | if_cond: RedND ⟨condition, s⟩ ⟨condition', s'⟩
      → RedND ⟨.eif condition e1 e2, s⟩ ⟨.eif condition' e1 e2, s'⟩

  | ewhile : RedND ⟨.ewhile c body, stx⟩ ⟨.eif c (.seq body (.ewhile c body)) .skip, stx⟩

theorem RedND_det (ha : RedND ⟨e, s⟩ ⟨e₁, s₁⟩ ) (hb : RedND ⟨e, s⟩ ⟨e₂, s₂⟩)
    : e₁ = e₂ ∧ s₁ = s₂ := by
  induction e generalizing e₁ s₁ e₂ s₂
  <;> try trivial
  case op lhs op rhs lhs_ih rhs_ih =>
    cases ha
    <;> cases hb
    <;> try trivial
    case op1.op1 ha _ hb =>
      obtain ⟨rfl, rfl⟩ := lhs_ih ha hb
      exact ⟨rfl, rfl⟩
    case op1b.op1b ha _ hb => 
      obtain ⟨rfl, rfl⟩ := rhs_ih ha hb
      exact ⟨rfl, rfl⟩
    case op1.op1b ha _ hb =>
      -- This goal is unprovable
      -- this is due to us being unable to specilize the inductive hypothesises
      -- Proof context:
      -- | s : VarMap
      -- | lhs : Expr
      -- | op : Op
      -- | rhs : Expr
      -- | lhs_ih : ∀ {e₁ : Expr} {s₁ : VarMap} {e₂ : Expr} {s₂ : VarMap},
      -- |   RedND (lhs, s) (e₁, s₁) → RedND (lhs, s) (e₂, s₂) → e₁ = e₂ ∧ s₁ = s₂
      -- | rhs_ih : ∀ {e₁ : Expr} {s₁ : VarMap} {e₂ : Expr} {s₂ : VarMap},
      -- |   RedND (rhs, s) (e₁, s₁) → RedND (rhs, s) (e₂, s₂) → e₁ = e₂ ∧ s₁ = s₂
      -- | s₁ s₂ : VarMap
      -- | e'✝ : Expr
      -- | ha : RedND (lhs, s) (e'✝, s₁)
      -- | e2'✝ : Expr
      -- | hb : RedND (rhs, s) (e2'✝, s₂)
      -- | ⊢ e'✝.op op rhs = lhs.op op e2'✝ ∧ s₁ = s₂
      sorry
    case op1b.op1 ha _ hb =>
      -- likewise here
      sorry
  case eif c t f c_ih t_ih f_ih => sorry
  case ewhile c e c_ih e_ih => sorry
  case assign addr e e_ih => sorry
  case deref addr => sorry
  case seq a b a_ih b_ih => sorry

end Q13

section Q135

#check Red.casesOn

end Q135

