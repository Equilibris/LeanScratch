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

def MuTy.reduce (n : ℕ) : MuTy → MuTy → MuTy
  | .unit, _ => .unit
  | .μ body, r => .μ (body.reduce n.succ r)
  | .prod a b, r => .prod (a.reduce n r) (b.reduce n r)
  | .sum a b, r => .sum (a.reduce n r) (b.reduce n r)
  | .bvar idx, r => match compare idx n with
    | .lt => .bvar idx
    | .eq => r
    | .gt => .bvar idx.pred

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

/- theorem MuTy.reduce_Valid (hfull : Valid 0 full) (hInd : Ind n.succ body) : Valid n (body.reduce n full) := match body with -/
/-   | .unit => .unit -/
/-   | .prod _ _ => .prod sorry sorry -/
/-   | .sum  _ _ => .sum sorry sorry -/
/-   | .bvar _ => by -/
/-     dsimp [reduce] -/
/-     split -/
/-     <;> rename_i h -/
/-     <;> simp only [Nat.compare_eq_eq, Nat.compare_eq_lt, Nat.compare_eq_gt] at h -/
/-     ? exact .bvar h -/
/-     ? refine Valid.lower ?_ hfull -/
/-       exact Nat.zero_le n -/
/-     ? cases hInd -/
/-       next hneq hlt => -/
/-       exact Valid.bvar (by omega) -/


inductive Expr (fΓ : List Ty) : /- bvar ctx -/ List MuTy → /- ? ctx -/ List MuTy → Ty → Type
  | unit : Expr _ _ _ (.direct .unit)
  | lam : Expr _ (argTy :: bvs) mΓ retTy
      → Expr _ bvs mΓ (.arr argTy retTy)
  | app : Expr _ bvs mΓ (.arr argTy retTy) → Expr _ bvs mΓ (.direct argTy)
      → Expr _ bvs mΓ retTy

  | bvar (n : ℕ) t : bvs[n]? = some t
      → Expr _ bvs mΓ (.direct t)
  | fvar (n : ℕ) t : fΓ[n]? = some t → Expr _ _ _ t

  | prod : Expr _ bvs mΓ (.direct a) → Expr _ bvs mΓ (.direct b)
      → Expr _ bvs mΓ (.direct (.prod a b))
  | inl : Expr _ bvs mΓ (.direct a)
      → Expr _ bvs mΓ (.direct $ .sum a b)
  | inr : Expr _ bvs mΓ (.direct a)
      → Expr _ bvs mΓ (.direct $ .sum b a)

  -- At this point we need to increment each of the arguments bvars in some way
  -- If this is not done the expression is false as the (.bvar 0) would refer to another type
  | enterMu : Expr _ bvs ((.μ body) :: mΓ.map (MuTy.incrementExposed 0 1)) (.direct body)
      → Expr _ bvs mΓ (.direct (.μ body))
  | exitMu : Expr _ bvs mΓ (.direct (.μ body))
      → Expr _ bvs mΓ (.direct (body.reduce 0 (.μ body)))

  | enterBMu : mΓ[idx]? = some t → Expr _ bvs mΓ (.direct t) →
      Expr _ bvs mΓ (.direct (.bvar idx))

  | ematch : Expr _ bvs mΓ (.direct (.sum a b)) →
             Expr _ (a :: bvs) mΓ (.direct t) → 
             Expr _ (b :: bvs) mΓ (.direct t)
      → Expr _ bvs mΓ (.direct t)
  | projl : Expr _ bvs mΓ (.direct (.prod a b))
      → Expr _ bvs mΓ (.direct a)
  | projr : Expr _ bvs mΓ (.direct (.prod a b))
      → Expr _ bvs mΓ (.direct b)

abbrev NatTy.add.Ty : Ty := .arr NatTy $ .arr NatTy $ .direct NatTy
abbrev NatTy.add : Expr [NatTy.add.Ty] [] [] NatTy.add.Ty :=
  .lam $ .lam $ .ematch
    (.exitMu (.bvar 0 NatTy $ by rfl))
    (.bvar 1 NatTy rfl)
    $ .ematch (.exitMu $ .bvar 2 NatTy $ by rfl)
      (.enterMu $ .inl .unit)
      $ .app (.app ( .fvar 0 NatTy.add.Ty rfl) $ .bvar 1 _ rfl)
      $ .bvar 0 _ rfl

def Expr.bvarShift (arg : Expr fΓ (bvs1 ++ bvs) mΓ t) : Expr fΓ (bvs1 ++ bvs2 ++ bvs) mΓ t := match arg with
  | .unit => .unit
  | .projr body => .projr body.bvarShift
  | .projl body => .projl body.bvarShift
  | .ematch scrutinee a b => .ematch scrutinee.bvarShift (
    let a : Expr _ ((_ :: _) ++ bvs) _ _ := a
    a.bvarShift) (
    let b : Expr _ ((_ :: _) ++ bvs) _ _ := b
    b.bvarShift)
  | .enterBMu p body => .enterBMu p body.bvarShift
  | .exitMu body => .exitMu body.bvarShift
  | .enterMu body => .enterMu body.bvarShift
  | .inr body => .inr body.bvarShift
  | .inl body => .inl body.bvarShift
  | .prod a b => .prod a.bvarShift b.bvarShift
  | .fvar _ _ p => .fvar _ _ p
  | .bvar n t p =>
    if h : n < bvs1.length then
      .bvar n t (by

        simp only [List.getElem?_append h, List.append_assoc] at p ⊢
        exact p)
    else
      .bvar (n + bvs2.length) t (by
        simp only [not_lt] at h
        simp only [List.append_assoc]
        apply Eq.trans $ List.getElem?_append_right $ h.trans $ Nat.le_add_right _ _
        rw [
          Nat.sub_add_comm h,
          List.getElem?_append_right (Nat.le_add_left _ _),
          Nat.add_sub_cancel
        ]
        rw [List.getElem?_append_right h] at p
        exact p)
  | .app a b => .app a.bvarShift b.bvarShift
  | .lam body => .lam (
    let body : Expr _ ((_ :: _) ++ bvs) _ _ := body
    body.bvarShift)

/- def Expr.increment : Expr fΓ bvs mΓ (.direct t) ? Expr fΓ (bvs) (addition :: mΓ) (.direct $ t.incrementExposed 0) -/
/-   | .unit => .unit -/
/-   | .prod a b => .prod a.increment b.increment -/
/-   | .projl body => .projl body.increment -/
/-   | .projr body => .projr body.increment -/
/-   | .ematch e l r => .ematch e l.increment r.increment -/
/-   | .enterBvar p x => .enterBvar sorry x.increment -/
/-   | .enterMu _ => sorry -/
/-   | .exitMu _ => sorry -/
/-   | .inr _ => sorry -/
/-   | .inl _ => sorry -/
/-   | .fvar _ _ _ => sorry -/
/-   | .bvar _ _ _ => sorry -/
/-   | .app _ _ => sorry -/

/- def MuTy.shifted (skip shift : ?) : MuTy ? MuTy -/
/-   | .unit => .unit -/
/-   | .bvar idx => sorry -/
/-   | .sum  a b => sorry -/
/-   | .prod a b => sorry -/
/-   | .? body => sorry -/

/- def Expr.?Shift : Expr fΓ bvs (mΓ₁ ++ m?) t ? Expr fΓ bvs (m?₁ ++ m?add ++ m?) t -/
/-   | .unit => .unit -/
/-   | .projr body => .projr body.?shift -/
/-   | .projl body => .projl body.?shift -/
/-   | .ematch scrutinee a b => .ematch scrutinee.?shift a.?shift b.?shift -/
/-   | @enterbvar _ _ t _ idx p body => -/
/-     sorry -/
/-     /- if h : idx < mγ₁.length then -/ -/
/-     /-   .enterbvar (by -/ -/
/-     /-     simp only [list.getelemΓ_append h, list.append_assoc] at p ? -/ -/
/-     /-     exact p) body.?shift -/ -/
/-     /- else -/ -/
/-     /-   .enterbvar (idx := idx) (by sorry) body.?shift -/ -/
/-   | .exitmu body => .exitmu body.?shift -/
/-   | @entermu _ _ b' _ body => .entermu ( -/
/-     let body : expr _ _ (((.? b') :: mγ₁) ++ mγ) (.direct b') := body -/
/-     body.?shift -/
/-   ) -/
/-   | .inr body => .inr body.?shift -/
/-   | .inl body => .inl body.?shift -/
/-   | .prod a b => .prod a.?shift b.?shift -/
/-   | .fvar _ _ p => .fvar _ _ p -/
/-   | .bvar _ _ p => .bvar _ _ p -/
/-   | .app a b => .app a.?shift b.?shift -/
/-   | .lam body => .lam body.?shift -/

-- F : * → *
-- μ F = F (μ F)

def Expr.growShiftGen :
    Expr fΓ bvs (mpre ++ (List.map (MuTy.incrementExposed 0 mpre.length) mΓ)) t →
    Expr fΓ bvs (mpre ++ (List.map (MuTy.incrementExposed 0 (mpre.length)) mx) ++ (List.map (MuTy.incrementExposed 0 ((mpre ++ mx).length)) mΓ)) (t.incrementExposed mpre.length mx.length)
  | .unit => .unit
  | .enterBMu (idx := idx) eq body =>
    /- .enterBvar eq body.growShift -/
    if idx < mpre.length then
      sorry
    else
      .enterBMu (idx := idx + mx.length) sorry body.growShiftGen
  | .enterMu body => 
    sorry
    /- by -/
    /- sorry -/
  | .exitMu body => .exitMu body.growShiftGen
  | .ematch c a b => .ematch c.growShiftGen a.growShiftGen b.growShiftGen
  | .projl body => .projl body.growShiftGen
  | .projr body => .projr body.growShiftGen
  | .inr body => .inr body.growShiftGen
  | .inl body => .inl body.growShiftGen
  | .prod a b => .prod a.growShiftGen b.growShiftGen
  | .fvar _ _ p => .fvar _ _ p
  | .bvar _ _ p => .bvar _ _ p
  | .app a b => .app a.growShiftGen b.growShiftGen
  | .lam body => .lam body.growShiftGen

def Expr.growShift (x : Expr fΓ bvs mΓ t)
    : Expr fΓ bvs (m ++ (List.map (MuTy.incrementExposed 0 (m.length)) mΓ)) t := by
  change Expr _ _ ([] ++ _ ++ _) _
  change Expr _ _ ([] ++ _) _ at x

  have x := Expr.growShiftGen (mpre := []) (mx := m) x
  simp only [List.length_nil, MuTy.incrementExposed_zero, List.map_id, List.nil_append] at x ⊢

  exact x


def Expr.bvarReplace
    : Expr fΓ (pls ++ hd :: bvs) (mΓ) t
    → Expr fΓ bvs mΓ (.direct hd)
    → Expr fΓ (pls ++ bvs) (mΓ) t
  | .unit, r => .unit
  | .projr body, r => .projr (Expr.bvarReplace body r)
  | .projl body, r => .projl (Expr.bvarReplace body r)
  | .ematch scrutinee a b, r => .ematch (scrutinee.bvarReplace r) (by
    change Expr _ ((_ :: pls) ++ bvs) _ _
    exact a.bvarReplace r) (by
    change Expr _ ((_ :: pls) ++ bvs) _ _
    exact b.bvarReplace r)
  | .enterBMu v body, r => .enterBMu v (body.bvarReplace r)
  | .exitMu body, r => .exitMu (body.bvarReplace r)
  | .enterMu (body := bodyT) body, r => .enterMu
    (body.bvarReplace $ Expr.growShift (m := [bodyT.μ]) r)
  | .inr body, r => .inr (body.bvarReplace r)
  | .inl body, r => .inl (body.bvarReplace r)
  | .prod a b, r => .prod (a.bvarReplace r) (b.bvarReplace r)
  | .fvar _ _ p, r => .fvar _ _ p
  | .bvar idx t p, r =>
    match h : compare idx pls.length with
    | .lt => .bvar idx t (by
      rw [List.getElem?_append (Nat.compare_eq_lt.mp h)] at p ⊢
      exact p)
    | .eq => by
      obtain rfl := Nat.compare_eq_eq.mp h

      have p := (List.getElem?_append_right (le_refl _)).symm.trans p
      rw [Nat.sub_self] at p
      have p := (Option.some.injEq _ _).mp $ List.getElem?_cons_zero.symm.trans p
      subst p

      exact r.bvarShift (bvs1 := []) (bvs2 := pls)
    | .gt => .bvar idx.pred t (by
      have := (Nat.compare_eq_gt.mp h)
      change (pls ++ ([hd] ++ bvs))[_]? = _ at p
      rw [←List.append_assoc] at p
      have p := (List.getElem?_append_right (by simp only [List.length_append, List.length]; exact this)).symm.trans p
      rw [List.length_append, Nat.add_comm, Nat.sub_add_eq] at p
      rw [List.getElem?_append_right (Nat.le_pred_of_lt this)]
      exact p)
  | .app a b , r => .app (a.bvarReplace r) (b.bvarReplace r)
  | .lam body, r =>
    let body : Expr _ (_ :: _ ++ _) _ _ := body
    .lam (body.bvarReplace r)

