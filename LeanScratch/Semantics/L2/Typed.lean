import LeanScratch.Semantics.L2.Stx
import LeanScratch.Semantics.L2.Red
import LeanScratch.Relation
import Mathlib.Data.List.AList

namespace L2

-- TODO: Change Int to Unit
abbrev RefCtx := AList fun _ : String => ℤ

inductive TySpec : RefCtx → List Ty → Expr → Ty → Prop
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
  | ref : (Γ'[idx]? = some w)
      → TySpec Γ Γ' (.bvar idx) w
  | abs : TySpec Γ (argTy :: Γ') body retTy
      → TySpec Γ Γ' (.abs argTy body) (.arrow argTy retTy)
  | app : TySpec Γ Γ' fn (.arrow argTy retType) → TySpec Γ Γ' arg argTy
      → TySpec Γ Γ' (.app fn arg) retType

  | letVal : TySpec Γ Γ' e t → TySpec Γ (t :: Γ') body t'
      → TySpec Γ Γ' (.letVal t e body) t'
  | letRecValFn : TySpec Γ (t1::(.arrow t1 t2)::Γ') e1 t2 → TySpec Γ ((.arrow t1 t2) :: Γ') e2 t
      → TySpec Γ Γ' (.letRecVal (.arrow t1 t2) (.abs t1 e1) e2) t

