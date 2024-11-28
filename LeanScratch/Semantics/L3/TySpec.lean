import LeanScratch.Semantics.L3.Stx

namespace L3

-- We need to use our function call smeantics
-- when we implement the typ signagure of L3 in this case
@[aesop safe [constructors, cases]]
inductive TySpec : List Ty → Expr → Ty → Prop
  | bool : TySpec Γ (.bool _) .bool
  | int  : TySpec Γ (.int  _) .int
  | skip : TySpec Γ .skip     .void

  | op_add : TySpec Γ e₁ .int →
             TySpec Γ e₂ .int
    → TySpec Γ (.op e₁ .add e₂) .int
  | op_gte : TySpec Γ e₁ .int →
             TySpec Γ e₂ .int
    → TySpec Γ (.op e₁ .gte e₂) .bool

  | eif : TySpec Γ scrutinee .bool →
          TySpec Γ a t →
          TySpec Γ b t
    → TySpec Γ (.eif scrutinee a b) t
  | ewhile : TySpec Γ' c .bool →
             TySpec Γ' e .void
    → TySpec Γ' (.ewhile c e) .void

  | ref : TySpec Γ (.ref t _) t.ref
  | loc : TySpec Γ (.loc t _) t.ref

  | assign : TySpec Γ addr t.ref →
             TySpec Γ e    t
    → TySpec Γ (.assign addr e) .void
  | deref : TySpec Γ addr t.ref
    → TySpec Γ (.deref addr) t

  | seq : TySpec Γ a .void → TySpec Γ b o
      → TySpec Γ (.seq a b) o

  | bvar : (Γ[idx]? = some w)
      → TySpec Γ (.bvar idx) w
  | abs : TySpec (argTy :: Γ) body retTy
      → TySpec Γ (.abs argTy body) (.arrow argTy retTy)
  | app : TySpec Γ fn (.arrow argTy retType) → TySpec Γ arg argTy
      → TySpec Γ (.app fn arg) retType

  | letVal : TySpec Γ expr argTy →
             TySpec (argTy :: Γ) body retTy
      → TySpec Γ (.letVal argTy expr body) (.arrow argTy retTy)

  | pair : TySpec Γ a aTy →
           TySpec Γ b bTy
      → TySpec Γ (.pair a b) (.prod aTy bTy)
  | fst : TySpec Γ a (.prod aTy bTy)
      → TySpec Γ (.fst a) aTy
  | snd : TySpec Γ a (.prod aTy bTy)
      → TySpec Γ (.snd a) bTy

  | inl : TySpec Γ a aTy
      → TySpec Γ (.inl bty a) (.sum aTy bTy)
  | inr : TySpec Γ b bTy
      → TySpec Γ (.inl aty b) (.sum aTy bTy)
  | case : TySpec Γ scrutinee (.sum aTy bTy) →
           TySpec (aTy :: Γ) a t →
           TySpec (bTy :: Γ) b t
      → TySpec Γ (.case scrutinee a b) t

theorem TySpec.unique (a : TySpec Γ e t) (b : TySpec Γ e t') : t = t' := by
  /- aesop? -/
  induction a generalizing t'
  <;> cases b
  <;> (try rfl)
  case eif s a b ihs iha ihb s' a' b' => exact iha a'
  case deref a ih a' => exact (Ty.ref.injEq _ _).mp $ ih a'
  case seq a b iha ihb a' b' => exact ihb b'
  case bvar a b => exact (Option.some.injEq _ _).mp $ a.symm.trans b
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry

