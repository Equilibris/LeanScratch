import LeanScratch.Semantics.L2.Stx
import LeanScratch.Semantics.L2.Red
import LeanScratch.Relation
import Mathlib.Data.List.AList

namespace L2

-- TODO: Change Int to Unit
abbrev RefCtx := AList fun _ : String => ℤ
abbrev AbsCtx := AList fun _ : String => Ty

inductive TySpec : RefCtx → AbsCtx → Expr → Ty → Prop
  | bool : TySpec Γ Γ' (.bool b) .bool
  | int  : TySpec Γ Γ' (.int i)  .int
  | skip : TySpec Γ Γ' .skip     .void

  | op_add : TySpec Γ Γ' a .int → TySpec Γ Γ' b .int
      → TySpec Γ Γ' (.op a .add b) .int
  | op_gte : TySpec Γ Γ' a .int → TySpec Γ Γ' b .int
      → TySpec Γ Γ' (.op a .gte b) .bool

  | deref : (h : ∃ w, Γ.lookup addr = some w)
      → TySpec Γ Γ' (.deref addr) .int
  | assign : (h : ∃ w, Γ.lookup addr = some w) → TySpec Γ Γ' e .int
      → TySpec Γ Γ' (.assign addr e) .void
  | seq : TySpec Γ Γ' a .void → TySpec Γ Γ' b o
      → TySpec Γ Γ' (.seq a b) o

  | eif : TySpec Γ Γ' c .bool → TySpec Γ Γ' t a → TySpec Γ Γ' f a
      → TySpec Γ Γ' (.eif c t f) a

  | ewhile : TySpec Γ Γ' c .bool → TySpec Γ Γ' body .void
      → TySpec Γ Γ' (.ewhile c body) .void

  -- Should this be ∃ quantified?
  | ref : (Γ'.lookup name = some w)
      → TySpec Γ Γ' (.ref name) w
  | abs : TySpec Γ (Γ'.insert name argTy) body retTy
      → TySpec Γ Γ' (.abs name argTy body) (.arrow argTy retTy)
  | app : TySpec Γ Γ' fn (.arrow argTy retType) → TySpec Γ Γ' arg argTy
      → TySpec Γ Γ' (.app fn arg) retType

@[simp]
theorem BoolEx : TySpec Γ Γ' (Expr.bool b) Ty.bool := .bool
@[simp]
theorem IntEx : TySpec Γ Γ' (Expr.int v) Ty.int := .int
@[simp]
theorem SkipEx : TySpec Γ Γ' (Expr.skip) Ty.void := .skip
@[simp]
theorem OpEx (ha : TySpec Γ Γ' a .int) (hb : TySpec Γ Γ' b .int): TySpec Γ Γ' (.op a o b) (match o with | .add => .int | .gte => .bool) :=
  match o with 
  | .add => .op_add ha hb
  | .gte => .op_gte ha hb

@[simp]
theorem OpAddEx (ha : TySpec Γ Γ' a .int) (hb : TySpec Γ Γ' b .int) : TySpec Γ Γ' (.op a .add b) .int  := OpEx ha hb
@[simp]
theorem OpGteEx (ha : TySpec Γ Γ' a .int) (hb : TySpec Γ Γ' b .int) : TySpec Γ Γ' (.op a .gte b) .bool := OpEx ha hb


theorem TyUnique : TySpec Γ Γ' i o₁ ∧ TySpec Γ Γ' i o₂ → o₁ = o₂ := by
  rintro ⟨a, b⟩

  induction a generalizing o₂
  <;> cases b
  <;> try simp_all only [Ty.arrow.injEq, true_and, Option.some.injEq]
  case seq b_ih _ ba =>
    exact b_ih ba
  case eif t_ih _ _ ta _ =>
    exact t_ih ta
  case abs a_ih _ a =>
    exact a_ih a
  case app a_ih _ _ _ fna =>
    injection a_ih fna

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

theorem CtxConsistency (trans : Red ⟨e, s⟩ ⟨e', s'⟩) (a : TySpec s Γ' w x) : TySpec s' Γ' w x := by
  induction a
  · exact .bool
  · exact .int
  · exact .skip
  case op_add a b => exact .op_add (a trans) (b trans)
  case op_gte a b => exact .op_gte (a trans) (b trans)
  case deref h =>
    exact .deref (AddrConsistency trans h)
  case assign h _ deeper =>
    exact .assign (AddrConsistency trans h) (deeper trans)
  case seq a b => exact .seq (a trans) (b trans)
  case eif c t f => exact .eif (c trans) (t trans) (f trans)
  case ewhile c b => exact .ewhile (c trans) (b trans)
  case ref a => exact .ref a
  case abs a_ih => exact .abs (a_ih trans)
  case app a b => exact .app (a trans) (b trans)

theorem NonFreeAddition (h : name ∉ e.v) : TySpec Γ Γ' e ty ↔ TySpec Γ (Γ'.insert name w) e ty := by
  constructor
  <;> intro ha
  · induction ha
    <;> simp only [Expr.v, Finset.not_mem_empty, not_false_eq_true, Finset.mem_union, not_or, Finset.mem_singleton] at h
    · simp only [BoolEx]
    · simp only [IntEx]
    · simp only [SkipEx]
    case op_add lih rih =>
      rcases h with ⟨l, r⟩
      exact OpAddEx (lih l) (rih r)
    case op_gte lih rih =>
      rcases h with ⟨l, r⟩
      exact OpGteEx (lih l) (rih r)
    case deref v  => exact .deref v
    case assign v _ ih => exact .assign v (ih h)
    case seq aih bih =>
      rcases h with ⟨a, b⟩
      exact .seq (aih a) (bih b)
    case eif cih tih fih =>
      rcases h with ⟨⟨c,t⟩, f⟩
      exact .eif (cih c) (tih t) (fih f)
    case ewhile cih eih =>
      rcases h with ⟨c, e⟩
      exact .ewhile (cih c) (eih e)
    case ref w' Γ Γ' name a =>
      rename_i name' _ _
      have : AList.lookup name (AList.insert name' w Γ') = some w' := by
        change _ ≠ _ at h
        rw [AList.lookup_insert_ne h.symm]
        exact a
      exact .ref this
    case abs Γ' name' argTy a a_ih =>
      rcases h with ⟨h₁, h₂⟩
      have := a_ih h₁
      change _ ≠ _ at h₂

      suffices x : (Γ'.insert name' argTy).insert name w = (Γ'.insert name w).insert name' argTy by
        rw [x] at this
        exact .abs this
      have : ((Γ'.insert name' argTy).insert name w).entries.Perm ((Γ'.insert name w).insert name' argTy).entries := AList.insert_insert_of_ne Γ' h₂.symm
      ext
      rename_i n a
      have := @AList.mem_of_perm _ _ _ _ _ _ this
      sorry
    case app aih bih =>
      rcases h with ⟨a, b⟩
      exact .app (aih a) (bih b)
  · sorry

theorem TypeClosedUnderAlpha (h : TySpec Γ Γ' e ty) (post_not_free : post ∉ e.fv)
    : TySpec Γ (if let some w := Γ'.lookup pre then Γ'.insert post w else Γ') (e.α pre post) ty := by
  induction h -- generalizing
  <;> simp only [Expr.α]
  <;> simp only [Expr.fv, Finset.not_mem_empty, not_false_eq_true, Finset.mem_sdiff, Finset.mem_singleton, not_and, Decidable.not_not, Finset.union_assoc, Finset.mem_union, not_or] at post_not_free
  · exact .bool
  · exact .int
  · exact .skip
  case op_add lhs rhs =>
    simp_all only [not_false_eq_true, true_implies]
    exact .op_add lhs rhs
  case op_gte lhs rhs =>
    simp_all only [not_false_eq_true, true_implies]
    exact .op_gte lhs rhs
  case deref h =>
    exact .deref h
  case assign h _ ih =>
    exact .assign h (ih post_not_free)
  case seq a b =>
    simp_all only [not_false_eq_true, true_implies]
    exact .seq a b
  case eif c t f =>
    simp_all only [not_false_eq_true, true_implies]
    exact .eif c t f 
  case ewhile c b =>
    simp_all only [not_false_eq_true, true_implies]
    exact .ewhile c b
  case ref wx _ Γ' name a =>
    by_cases h : name = pre
    · rw [h] at a
      simp only [←h, a, ↓reduceIte]
      have {x} : (AList.insert post x Γ').lookup post = some x := by simp only [AList.lookup_insert]
      exact .ref this
    · simp [h]
      by_cases h : ∃ w, Γ'.lookup pre = some w
      · rcases h with ⟨w, p⟩
        simp only [p]
        suffices x : AList.lookup name (AList.insert post w Γ') = some wx from .ref x
        change _ ≠ _ at post_not_free
        simp only [AList.lookup_insert_ne post_not_free.symm, a]
      · simp_all only [← Option.ne_none_iff_exists', ne_eq, Decidable.not_not]
        exact .ref a

  case abs Γ body retTy Γ' name argTy a ih =>
    sorry
    /- by_cases h :  -/
    /- by_cases h : name = pre -/
    /- · rw [h] at a -/
    /-   simp only [←h, a, ↓reduceIte] -/
    /-   suffices h : TySpec Γ (AList.insert name argTy (match AList.lookup pre Γ' with | some w => AList.insert post w Γ' | x => Γ')) body retTy from .abs h -/
    /-   by_cases h : ∃ w, Γ'.lookup pre = some w -/
    /-   · rcases h with ⟨w, p⟩ -/
    /-     simp only [p] -/
    /-     sorry -/
    /-   · simp_all only [← Option.ne_none_iff_exists', ne_eq, Decidable.not_not] -/
    /- · simp [h] -/
    /-   by_cases h : ∃ w, Γ'.lookup pre = some w -/
    /-   · rcases h with ⟨w, p⟩ -/
    /-     simp only [p] -/
    /-     suffices x : AList.lookup name (AList.insert post w Γ') = some wx from .ref x -/
    /-     change _ ≠ _ at post_not_free -/
    /-     simp only [AList.lookup_insert_ne post_not_free.symm, a] -/
    /-   · simp_all only [← Option.ne_none_iff_exists', ne_eq, Decidable.not_not] -/
    /-     exact .ref a -/
  case app a b =>
    simp_all only [not_false_eq_true, true_implies]
    exact .app a b

#exit

/- lemma ValuesGeneralizeContext (a : e.isFnValue) (h : TySpec Γ Γ' e ty) : ∀ n t,  -/

/- Really interesting observation:
   Originally I was trying to prove this theorem without `argIsVal`.
   When I was doing this I encountered the issue that in the application name ne case I had to prove:

   >  name' : String
   >  repl : Expr
   >  name : String
   >  ty : Ty
   >  body : Expr
   >  nne : ¬name' = name
   >  ih : ∀ {Γ : RefCtx} {Γ' : AbsCtx} {argTy retTy : Ty},
   >    TySpec Γ Γ' repl argTy → TySpec Γ (AList.insert name' argTy Γ') body retTy → TySpec Γ Γ' (body.subst name' repl) retTy
   >  Γ : RefCtx
   >  Γ' : AbsCtx
   >  argTy : Ty
   >  argh : TySpec Γ Γ' repl argTy
   >  retTy : Ty
   >  h : TySpec Γ (AList.insert name ty (AList.insert name' argTy Γ')) body retTy
   >  ⊢ TySpec Γ Γ' (Expr.abs name ty (body.subst name' repl)) (ty.arrow retTy)

  This is not the case as it is quite hard (possibly impossible) to construct the context needed to apply `ih _ h`.
  To fix this we need a lemma that the repl does not contain the name of the function arg being replaced.
  This means that our defn of `Expr.subst` is actually false for CBN langauges as an α-reduction would be required.
  This could either be done using De Bujin indicies or simply garuangteeing that you can do such a transfomration.
  As we are operating in a CBV langauge we can make this a lot simpler by asserting the arg is a value.
  Overall really cool and makes me want to implment a CBN langauge with a correct defn of `subst`.
  This would actually need a formalized definition of free variables something that currently we do not need.
  Overall just a fun observation and I recomend anyone reading to try this.
-/
theorem SubstTypePreservation (argIsVal : arg.isFnValue) (h : TySpec Γ Γ' (.app (.abs name argTy body) arg) retTy)  : TySpec Γ Γ' (body.subst name arg) retTy := by
  cases h
  case app argTy argh absh =>
  cases absh
  case abs absh =>
  induction body, name, arg using Expr.subst.induct generalizing argTy retTy Γ Γ'
  <;> simp only [Expr.subst, ↓reduceIte]
  <;> cases absh
  next => exact .bool
  next => exact .int
  next => exact .skip
  /- next lhs_ih rhs_ih => -/
    /- cases absh -/
  case case4.op_add lhs_ih rhs_ih lhs rhs=>
    exact .op_add (lhs_ih argIsVal argh lhs) (rhs_ih argIsVal argh rhs)
  case case4.op_gte lhs_ih rhs_ih lhs rhs =>
    exact .op_gte (lhs_ih argIsVal argh lhs) (rhs_ih argIsVal argh rhs)
  next cond_ih t_ih f_ih cond t f=>
    exact .eif (cond_ih argIsVal argh cond) (t_ih argIsVal argh t) (f_ih argIsVal argh f)
  next cond_ih body_ih cond body =>
    exact .ewhile (cond_ih argIsVal argh cond) (body_ih argIsVal argh body)
  next e_ih h e=>
    exact .assign h (e_ih argIsVal argh e)
  next h =>
    exact .deref h

  next a_ih b_ih a b=>
    exact .seq (a_ih argIsVal argh a) (b_ih argIsVal argh b)

  next h =>
    simp [AList.lookup_insert] at h
    rw [←h]
    exact argh

  next h a =>
    simp only [h, ↓reduceIte]
    change _ ≠ _ at h
    rw [AList.lookup_insert_ne h.symm] at a
    exact .ref a

  next a =>
    rw [AList.insert_insert] at a
    exact .abs a

  -- abs with ne typenames
  next name' repl name ty body nne ih retTy h =>
    simp only [nne, ↓reduceIte]
    sorry

    /- refine .abs (ih argh h) -/

    /- suffices v : TySpec Γ _ _ retTy from .abs v -/
    
    /- stop -/

    /- refine @ih Γ _ argTy _ ?_ ?_ -/
    /- · sorry -/
    /- · sorry -/


  next a_ih b_ih _ b a =>
    exact .app (a_ih argIsVal argh a) (b_ih argIsVal argh b)

theorem TypePreservation (h : Red ⟨e, s⟩ ⟨e', s'⟩) (pre : TySpec s Γ' e ty) : TySpec s' Γ' e' ty := by
  induction pre generalizing e' s'
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
  case app.beta preArg _ _ _ _ a _ _ =>
    sorry
    /- exact SubstTypePreservation (.app a preArg) -/
  case app.app1 a' b_ih a_ih e1' a =>
    exact .app (b_ih a) (CtxConsistency a a')
  case app.app2 ty₁ ty₂ b_ih a_ih _ fnIsVal a=>
    exact .app (CtxConsistency a ty₁) (a_ih a)

end L2

