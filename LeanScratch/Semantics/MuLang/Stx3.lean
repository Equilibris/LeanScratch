import Mathlib.Data.Nat.PSub
import Mathlib.Data.Rel
import Mathlib.Data.Vector.Basic
import LeanScratch.ListUtils


-- Inductive and broken datatypes,
-- a type like μ 0 is not valid
inductive MuTy : Type
  | unit : MuTy
  | bvar (idx : Nat)
  | sum  (a b : MuTy)
  | prod (a b : MuTy)
  | μ (body : MuTy)

mutual
inductive MuTy.Valid : ℕ → MuTy → Prop
  | unit : Valid n .unit
  | bvar : idx < n → Valid n (.bvar idx)
  | prod : Valid n a → Valid n b → Valid n (.prod a b)
  | sum  : Valid n a → Valid n b → Valid n (.sum  a b)

  | μ : Ind n.succ body → Valid n (.μ body)


-- Not actually an inductivity requirement
inductive MuTy.Ind : ℕ → MuTy → Prop
  | unit : Ind n .unit
  | bvar : idx ≤ 0 → idx < n → Ind n (.bvar idx)
  | sum  : Valid n a → Valid n b → Ind n (.sum  a b)

  | prod : Ind n a → Ind n b → Ind n (.prod a b)
end

mutual
theorem MuTy.Ind.lower (hlt : n ≤ k) (prev : Ind n body) : Ind k body := match body, prev with
  | .unit, _=> .unit
  | .μ body, p => by cases p
  | .prod a b, .prod ha hb => .prod (Ind.lower hlt ha) (Ind.lower hlt hb)
  | .sum a b, .sum ha hb => .sum (Valid.lower hlt ha) (Valid.lower hlt hb)
  | .bvar idx, .bvar ha hb => .bvar ha (Nat.lt_of_lt_of_le hb hlt)
theorem MuTy.Valid.lower (hlt : n ≤ k) (prev : Valid n body) : Valid k body := match body, prev with
  | .unit, _=> .unit
  | .μ body, .μ hbody => .μ (Ind.lower (Nat.succ_le_succ hlt) hbody)
  | .prod a b, .prod ha hb => .prod (Valid.lower hlt ha) (Valid.lower hlt hb)
  | .sum a b, .sum ha hb => .sum (Valid.lower hlt ha) (Valid.lower hlt hb)
  | .bvar idx, .bvar h => .bvar (Nat.lt_of_lt_of_le h hlt)
end

def MuTy.reduce (n : ℕ) : MuTy → MuTy → MuTy
  | .unit, _ => .unit
  | .μ body, r => .μ (body.reduce n.succ r)
  | .prod a b, r => .prod (a.reduce n r) (b.reduce n r)
  | .sum a b, r => .sum (a.reduce n r) (b.reduce n r)
  | .bvar idx, r => match compare idx n with
    | .lt => .bvar idx
    | .eq => r
    | .gt => .bvar idx.pred

theorem MuTy.Valid_of_Ind (v : Ind n body) : Valid n body := match body, v with
  | .bvar _ , .bvar _ a => .bvar a
  | .prod _ _ , .prod ha hb => .prod (Valid_of_Ind ha) (Valid_of_Ind hb)
  | .sum _ _, .sum ha hb => .sum ha hb
  | .unit, _ => .unit

-- Expresses types that have non-first class functions
inductive Ty
  | direct (body : MuTy) -- (h : body.Valid 0)
  | arr    (arg  : MuTy) -- (h :  arg.Valid 0)
           (ret : Ty)

-- This type is valid but not inductive
example : MuTy.Valid 0 (.μ (.sum (.bvar 0) (.bvar 0))) :=
  .μ (.sum (.bvar Nat.one_pos) (.bvar Nat.one_pos))

abbrev NatTy : MuTy := .μ (.sum .unit (.bvar 0))

theorem NatTy.Valid : MuTy.Valid 0 NatTy := .μ (.sum .unit (.bvar Nat.one_pos))

def MuTy.incrementExposed (skip inc : ℕ) : MuTy → MuTy
  | .unit => .unit
  | .μ body => .μ (body.incrementExposed skip.succ inc)
  | .prod a b => .prod (a.incrementExposed skip inc) (b.incrementExposed skip inc)
  | .sum a b => .sum (a.incrementExposed skip inc) (b.incrementExposed skip inc)
  | .bvar idx => if idx < skip then .bvar idx else .bvar $ idx + inc

theorem MuTy.increment_merge {t : MuTy}
    : (t.incrementExposed skip a).incrementExposed skip b = t.incrementExposed skip (a + b)
  := match t with
  | .unit => rfl
  | .bvar idx => by
    dsimp [incrementExposed]
    split
    next h =>
      simp only [
        incrementExposed,
        ite_eq_left_iff,
        bvar.injEq,
        add_right_eq_self]
      intro x
      exact False.elim (x h)
    next h =>
      dsimp [incrementExposed]
      split
      next h' =>
        have : idx < skip := calc
          idx ≤ idx + a := Nat.le_add_right idx a
          _ < skip := h'
        exact False.elim (h this)
      · rw [Nat.add_assoc]
  | .μ body => by
    dsimp [incrementExposed]
    rw [MuTy.increment_merge]
  | .prod a b => by
    dsimp [incrementExposed]
    rw [increment_merge, increment_merge]
  | .sum a b => by
    dsimp [incrementExposed]
    rw [increment_merge, increment_merge]

@[simp]
theorem MuTy.incrementExposed_zero : MuTy.incrementExposed skip 0 = id := by
  funext x
  induction x generalizing skip
  <;> simp_all only [incrementExposed, add_zero, ite_self, id_eq]

abbrev Ty.incrementExposed (skip inc : ℕ) : Ty → Ty
  | .direct term => .direct (term.incrementExposed skip inc)
  | .arr arg cont => .arr (arg.incrementExposed skip inc) (cont.incrementExposed skip inc)

inductive Expr : Type
  | unit
  | lam (arg : MuTy) (body : Expr)
  | app (fn arg : Expr)

  | bvar (n : ℕ)
  | fvar (n : ℕ)

  | prod (a b : Expr)
  | inl (other : MuTy) (body : Expr)
  | inr (other : MuTy) (body : Expr)

  -- At this point we need to increment each of the arguments bvars in some way
  -- If this is not done the expression is false as the (.bvar 0) would refer to another type
  | foldMu (t : MuTy) (body : Expr)
  | unfoldMu (body : Expr)

  | enterBMu (idx : ℕ) (body : Expr) 

  | ematch (scrutinee a b : Expr)
  | projl (body : Expr)
  | projr (body : Expr)

inductive TySpec (fΓ : List Ty) : /- bvar ctx -/ List MuTy → /- Γ ctx -/ List MuTy → Expr → Ty → Type
  | unit : TySpec fΓ _ _ .unit (.direct .unit)
  | lam : TySpec fΓ (argTy :: bvs) Γ body retTy
      → TySpec fΓ bvs Γ (.lam argTy body) (.arr argTy retTy)
  | app : TySpec _ bvs mΓ fn (.arr argTy retTy) → TySpec _ bvs mΓ arg (.direct argTy)
      → TySpec _ bvs mΓ (.app fn arg) retTy

  | bvar t : bvs[n]? = some t → TySpec fΓ bvs mΓ (.bvar n) (.direct t)
  | fvar t :  fΓ[n]? = some t → TySpec fΓ bvs mΓ (.fvar n) t

  | prod : TySpec _ bvs mΓ ea (.direct a) → TySpec _ bvs mΓ eb (.direct b)
      → TySpec _ bvs mΓ (.prod ea eb) (.direct (.prod a b))
  | inl : TySpec _ bvs mΓ body (.direct a)
      → TySpec _ bvs mΓ (.inl b body) (.direct $ .sum a b)
  | inr : TySpec _ bvs mΓ body (.direct b)
      → TySpec _ bvs mΓ (.inr a body) (.direct $ .sum a b)

  -- Rather than having increment exposed here, we can move it to only when we use the expr and then keep this static
  | foldMu : TySpec _ bvs ((.μ body) :: mΓ) e (.direct body)
      → TySpec _ bvs mΓ (.foldMu body e) (.direct (.μ body))
  | unfoldMu : TySpec _ bvs mΓ e (.direct (.μ body))
      → TySpec _ bvs mΓ (.unfoldMu e) (.direct (body.reduce 0 (.μ body)))

  | enterBMu : mΓ[idx]? = some t → TySpec _ bvs mΓ body (.direct $ t.incrementExposed 0 idx)
      → TySpec _ bvs mΓ (.enterBMu idx body) (.direct (.bvar idx))


  | ematch : TySpec fΓ bvs mΓ scrutinee (.direct $ .sum a b) →
             TySpec fΓ (a :: bvs) mΓ ea t →
             TySpec fΓ (b :: bvs) mΓ eb t
      → TySpec fΓ bvs mΓ (.ematch scrutinee ea eb) t

  | projl : TySpec _ bvs mΓ body (.direct $ .prod a b)
      → TySpec _ bvs mΓ (.projl body) (.direct a)
  | projr : TySpec _ bvs mΓ body (.direct $ .prod a b)
      → TySpec _ bvs mΓ (.projr body) (.direct b)

theorem TySpec.unique (a : TySpec fΓ bvs mΓ expr t) (b : TySpec fΓ bvs mΓ expr t') : t = t' :=
  match expr with
  | .unit => match a, b with | .unit, .unit => rfl
  | .lam ty body => match a, b with | .lam ax, .lam bx => (Ty.arr.injEq _ _ _ _).mpr ⟨rfl, TySpec.unique ax bx⟩
  | .app fn arg => match a, b with | .app xa ya, .app xb yb => ((Ty.arr.injEq _ _ _ _).mp (TySpec.unique xa xb)).2

  | .bvar n => match a, b with | .bvar _ a, .bvar _ b => (Ty.direct.injEq _ _).mpr $ (Option.some.injEq _ _).mp $ a.symm.trans b
  | .fvar n => match a, b with | .fvar _ a, .fvar _ b => (Option.some.injEq _ _).mp $ a.symm.trans b

  | .prod _ _ => match a, b with | .prod xa ya, .prod xb yb => (Ty.direct.injEq _ _).mpr
    $ (MuTy.prod.injEq _ _ _ _).mpr ⟨(Ty.direct.injEq _ _).mp
    $ TySpec.unique xa xb, (Ty.direct.injEq _ _).mp $ TySpec.unique ya yb⟩
  | .inl _ _ => match a, b with | .inl a, .inl b => (Ty.direct.injEq _ _ ).mpr $ (MuTy.sum.injEq _ _ _ _).mpr ⟨(Ty.direct.injEq _ _).mp $ TySpec.unique a b, rfl⟩
  | .inr _ _ => match a, b with | .inr a, .inr b => (Ty.direct.injEq _ _ ).mpr $ (MuTy.sum.injEq _ _ _ _).mpr ⟨rfl, (Ty.direct.injEq _ _).mp $ TySpec.unique a b⟩

  | .foldMu t body => match a, b with | .foldMu a, .foldMu b => (Ty.direct.injEq _ _).mpr $ (MuTy.μ.injEq _ _).mpr rfl
  | .unfoldMu body => match a, b with | .unfoldMu a, .unfoldMu b => (by rw [(MuTy.μ.injEq _ _).mp $ (Ty.direct.injEq _ _).mp $ TySpec.unique a b])

  | .enterBMu idx body => match a, b with | .enterBMu _ a, .enterBMu _ b => rfl

  | .ematch _ _ _ => match a, b with | .ematch as aa ab, .ematch bs ba bb => (by
    obtain ⟨rfl, rfl⟩ := (MuTy.sum.injEq _ _ _ _).mp $ (Ty.direct.injEq _ _).mp $ TySpec.unique as bs
    exact TySpec.unique aa ba)
  | .projl body => match a, b with | .projl a, .projl b => (Ty.direct.injEq _ _).mpr ((MuTy.prod.injEq _ _ _ _).mp $ (Ty.direct.injEq _ _).mp $ TySpec.unique a b).1
  | .projr body => match a, b with | .projr a, .projr b => (Ty.direct.injEq _ _).mpr ((MuTy.prod.injEq _ _ _ _).mp $ (Ty.direct.injEq _ _).mp $ TySpec.unique a b).2


theorem TySpec.allEq (a b : TySpec fΓ bvs mΓ expr t) : a = b :=
  match expr with
  | .unit => match a, b with | .unit, .unit => rfl
  | .lam ty body => match a, b with | .lam a, .lam b => (TySpec.lam.injEq _ _).mpr $ TySpec.allEq a b
  | .app fn arg => match a, b with | .app xa ya , .app xb yb => (by
    obtain ⟨rfl, _⟩ := (Ty.arr.injEq _ _ _ _).mp $ TySpec.unique xa xb
    rw [TySpec.allEq xa xb, TySpec.allEq ya yb])

  | .bvar n => match a, b with | .bvar _ _, .bvar _ _  => rfl
  | .fvar n => match a, b with | .fvar _ _, .fvar _ _  => rfl

  | .prod _ _ => match a, b with | .prod xa ya, .prod xb yb => (TySpec.prod.injEq _ _ _ _).mpr ⟨(TySpec.allEq xa xb), (TySpec.allEq ya yb)⟩
  | .inl _ _ => match a, b with | .inl a, .inl b => (TySpec.inl.injEq _ _).mpr (TySpec.allEq a b)
  | .inr _ _ => match a, b with | .inr a, .inr b => (TySpec.inr.injEq _ _).mpr (TySpec.allEq a b)

  | .foldMu t body => match a, b with | .foldMu a, .foldMu b => (TySpec.foldMu.injEq _ _).mpr (TySpec.allEq a b)
  | .unfoldMu body => sorry

  | .enterBMu idx body => sorry

  | .ematch scrutinee a b => sorry
  | .projl body => sorry
  | .projr body => sorry
  /- | .unit => sorry -/
  /- | .lam ty body => sorry -/
  /- | .app fn arg => sorry -/

  /- | .bvar n => sorry -/
  /- | .fvar n => sorry -/

  /- | .prod a b => sorry -/
  /- | .inl a => sorry -/
  /- | .inr a => sorry -/

  /- | .foldMu body => sorry -/
  /- | .unfoldMu body => sorry -/

  /- | .enterBMu idx body => sorry -/

  /- | .ematch scrutinee a b => sorry -/
  /- | .projl body => sorry -/
  /- | .projr body => sorry -/

def Expr.bvarShift (skip shift : ℕ) : Expr → Expr
  | .unit => .unit
  | .lam ty body => .lam ty $ body.bvarShift skip.succ shift
  | .app fn arg => .app (fn.bvarShift skip shift) (arg.bvarShift skip shift)

  | .bvar n =>
    if n < skip then .bvar n
    else .bvar $ n + shift
  | .fvar n => .fvar n

  | .prod a b => .prod (a.bvarShift skip shift) (b.bvarShift skip shift)
  | .inl b a => .inl b $ a.bvarShift skip shift
  | .inr a b => .inr a $ b.bvarShift skip shift

  | .foldMu t body => .foldMu t $ body.bvarShift skip shift
  | .unfoldMu body => .unfoldMu $ body.bvarShift skip shift

  | .enterBMu idx body => .enterBMu idx (body.bvarShift skip shift)

  | .ematch scrutinee a b => .ematch (scrutinee.bvarShift skip shift) (a.bvarShift skip.succ shift) (b.bvarShift skip.succ shift)
  | .projl body => .projl $ body.bvarShift skip shift
  | .projr body => .projr $ body.bvarShift skip shift

def TySpec.bvarShift
    (prev : TySpec fΓ (bvs1 ++ bvs) mΓ e t)
    : TySpec fΓ (bvs1 ++ bvs2 ++bvs) mΓ (e.bvarShift bvs1.length bvs2.length) t :=
  match prev with
  | .unit => .unit
  | .lam body =>
    let body : TySpec fΓ ((_ :: bvs1) ++ bvs) mΓ _ _ := body
    .lam (body.bvarShift)
  | .app fn arg =>
    .app fn.bvarShift arg.bvarShift

  | .bvar _ p => by
    dsimp [Expr.bvarShift]
    split
    next h =>
      apply TySpec.bvar
      simp only [List.getElem?_append h, List.append_assoc] at p ⊢
      exact p
    next h => 
      apply TySpec.bvar
      simp only [not_lt] at h
      simp only [List.append_assoc]
      apply Eq.trans $ List.getElem?_append_right $ h.trans $ Nat.le_add_right _ _
      rw [
        Nat.sub_add_comm h,
        List.getElem?_append_right (Nat.le_add_left _ _),
        Nat.add_sub_cancel
      ]
      rw [List.getElem?_append_right h] at p
      exact p
  | .fvar _ p => .fvar _ p

  | .prod a b => .prod a.bvarShift b.bvarShift
  | .inl a => .inl a.bvarShift
  | .inr a => .inr a.bvarShift

  | .foldMu body => .foldMu body.bvarShift
  | .unfoldMu body => .unfoldMu body.bvarShift

  | .enterBMu idx body => .enterBMu idx body.bvarShift

  | .ematch scrutinee a b =>
    let a : TySpec fΓ ((_ :: bvs1) ++ bvs) mΓ _ _ := a
    let b : TySpec fΓ ((_ :: bvs1) ++ bvs) mΓ _ _ := b
    .ematch scrutinee.bvarShift a.bvarShift b.bvarShift
  | .projl body => .projl body.bvarShift
  | .projr body => .projr body.bvarShift

-- benjamin peers types and programming langagues, equirecursive and isorecursive types
-- Talk to : Mevan (french surname)

/-- info: 'TySpec.bvarShift' depends on axioms: [propext] -/
#guard_msgs in #print axioms TySpec.bvarShift

