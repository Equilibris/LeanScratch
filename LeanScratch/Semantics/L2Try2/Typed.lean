import LeanScratch.Semantics.L2Try2.Stx
import LeanScratch.Semantics.L2Try2.Red
import LeanScratch.Relation
import Mathlib.Data.List.AList

namespace L2

-- TODO: Change Int to Unit
abbrev RefCtx := AList fun _ : String => ℤ

inductive TySpec : RefCtx → List Ty → BIdxExpr → Ty → Prop
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

  | ref : (h : v < Γ'.length)
      → TySpec Γ Γ' (.ref v) (Γ'[v]'h)
  | abs : TySpec Γ (argTy :: Γ') body retTy
      → TySpec Γ Γ' (.abs argTy body) (.arrow argTy retTy)
  | app : TySpec Γ Γ' fn (.arrow argTy retType) → TySpec Γ Γ' arg argTy
      → TySpec Γ Γ' (.app fn arg) retType

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

/- theorem TypePreservation.beta' (v : Red ) : sorry := by sorry -/

theorem TypePreservation.beta (ha : TySpec Γ Γ' arg argty)
    (a_ih : ∀ {e' : BIdxExpr} {s' : VarMap}, Red (arg, Γ) (e', s') → TySpec s' Γ' e' argty)
    (hb : TySpec Γ Γ' (BIdxExpr.abs ty body) (argty.arrow retType))
    (b_ih :
      ∀ {e' : BIdxExpr} {s' : VarMap}, Red (BIdxExpr.abs ty body, Γ) (e', s') → TySpec s' Γ' e' (argty.arrow retType))
    (argIsFn : arg.isFnValue)
    : TySpec Γ Γ' (BIdxExpr.replace n body arg) retType := by
  clear a_ih b_ih
  induction body generalizing retType argty ty Γ' n
  <;> simp only [BIdxExpr.replace]
  <;> cases hb
  case bool z =>
    cases z
    exact .bool
  case int z =>
    cases z
    exact .int
  case skip z =>
    cases z
    exact .skip
  case op o _ lhs_ih rhs_ih z =>
    cases o
    <;> cases z
    case op_add lhsTy rhsTy =>
      exact .op_add
        (lhs_ih ha (.abs lhsTy))
        (rhs_ih ha (.abs rhsTy))
    case op_gte lhsTy rhsTy =>
      exact .op_gte
        (lhs_ih ha (.abs lhsTy))
        (rhs_ih ha (.abs rhsTy))
  case eif cond_ih t_ih f_ih z =>
    cases z
    next cond t f =>
    exact .eif
      (cond_ih ha (.abs cond))
      (t_ih ha (.abs t))
      (f_ih ha (.abs f))
  case ewhile cond_ih e_ih z =>
    cases z
    next cond e =>
    refine .ewhile
      (cond_ih ha (.abs cond))
      ?_
    sorry
      /- (e_ih ha (.abs e)) -/
  case assign e_ih z =>
    cases z
    next h e =>
    exact .assign h (e_ih ha (.abs e))
  case deref z =>
    cases z
    next h =>
    exact TySpec.deref h
  case seq ha_ih hb_ih z =>
    cases z
    next x y =>
    exact .seq (ha_ih ha (.abs x)) (hb_ih ha (.abs y))
  case ref idx z =>
    split
    case isTrue  h =>
      rw [←h] at z
      cases z
      exact ha
    case isFalse h =>
      cases z
      next z =>
      refine .ref ?_
      sorry
  case abs ty body body_ih z =>
    cases z
    next retTy hbody =>
    refine (.abs (body_ih ?_ (.abs hbody)))
    /- sorry -/
    /- refine .abs ?_ -/
    /- apply body_ih (CtxConsistency h) -/
  case app fn_ih arg_ih z =>
    cases z
    next harg hfn =>
    exact .app (fn_ih ha (.abs hfn)) (arg_ih ha (.abs harg))

theorem TypePreservation : Red ⟨e, s⟩ ⟨e', s'⟩ → TySpec s Γ e x → TySpec s' Γ e' x := by
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
  case app.beta Γ Γ' argty retType arg ha a_ih ty body hb b_ih argIsFn =>
    exact TypePreservation.beta ha a_ih hb b_ih argIsFn
  case app.app1 z a_ih b_ih e1' ha =>
    exact .app (a_ih ha) (CtxConsistency ha z)
  case app.app2 x y a_ih b_ih e2' aIsFnVal ha =>
    exact .app (CtxConsistency ha x) (b_ih ha)


end L2
