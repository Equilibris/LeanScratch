import Mathlib.Init.Set
import Mathlib.Util.WhatsNew

inductive Vec (T : Type u) : Nat → Type u
  | nil : Vec T 0
  | cons (hd : T) (tl : Vec T n) : Vec T (n.succ)

infixr:20 " %:: " => Vec.cons
notation:20 "%[]" => Vec.nil

syntax "%[" ( term ),+ "]" : term
-- Unexpanders are pain. Can't be fuqd
macro_rules
  | `(%[$hd:term]) => `(Vec.cons $hd Vec.nil)
  | `(%[$hd:term, $rest,*]) => `(Vec.cons $hd (%[ $rest,* ]))

/-- info: 10 %:: 20 %:: 30 %:: %[] : Vec Nat (Nat.succ 0).succ.succ -/
#guard_msgs in #check %[10, 20, 30]

def Vec.map (f : α → β) : Vec α n → Vec β n
  | %[] => %[]
  | hd %:: tl => f hd %:: tl.map f

instance : Functor (Vec · n) where map := Vec.map
instance : LawfulFunctor (Vec · n) where
  id_map x := by
    induction x
    · rfl
    next ih =>
      dsimp [Functor.map, Vec.map] at ih ⊢
      rw [ih]
  comp_map f g x := by
    induction x
    · rfl
    · next ih =>
      dsimp [Functor.map, Vec.map] at ih ⊢
      rw [ih]
  map_const := rfl

inductive Term {Nm : Type} (V : Type) (Arity : Nm → Nat)
  | var   (nm : V)
  | const (nm : Nm) (app : Vec (Term V Arity) (Arity nm))

/-

def Term.bound {Arity : Nm → Nat} (nm : Nm) (x : Term Arity) : Prop :=
  match x with
  | .const _ => False
  | .var n children =>
    n = nm ∨ trev children
    where
      trev {n} : Vec _ n → Prop
        | .nil => False
        | .cons hd tl => (bound nm hd) ∨ (trev tl)

def Term.bound.dec {Arity : Nm → Nat} (term : Term Arity) [DecidableEq Nm] (nm : Nm) : Decidable (Term.bound nm term) :=
  match term with
  | .const _ => .isFalse (by simp only [bound, not_false_eq_true])
  | .var n ls =>
    if h : n = nm then
      .isTrue (by simp only [bound, h, true_or])
    else
      match trev_dec ls with
      | .isTrue p => .isTrue (by simp only [bound, p, or_true])
      | .isFalse p => .isFalse (by simp only [bound, h, p, or_self, not_false_eq_true])
      where
        trev_dec {n} (v : Vec (Term Arity) n) : Decidable (trev nm v) :=
          match v with
          | .nil => .isFalse (by simp only [trev, not_false_eq_true])
          | .cons hd tl =>
            match dec hd nm with
            | .isTrue p => .isTrue (by simp only [Nat.succ_eq_add_one, trev, p, true_or])
            | .isFalse p =>
              match trev_dec tl with
              | .isTrue p' => .isTrue (by simp only [Nat.succ_eq_add_one, trev, p', or_true])
              | .isFalse p' => .isFalse (by simp only [Nat.succ_eq_add_one, trev, p, p', or_self,
                not_false_eq_true])

instance [DecidableEq Nm] {nm : Nm} : Decidable (Term.bound nm term) := Term.bound.dec term nm

-/

inductive Formula V (TA : TNm → Nat) (PA : PNm → Nat)
  | pred (nm : PNm) (app : Vec (Term V TA) (PA nm))

  | univ (nm : V) : Formula V TA PA → Formula V TA PA
  | exis (nm : V) : Formula V TA PA → Formula V TA PA

  | conj : Formula V TA PA → Formula V TA PA → Formula V TA PA
  | disj : Formula V TA PA → Formula V TA PA → Formula V TA PA
  | imp  : Formula V TA PA → Formula V TA PA → Formula V TA PA
  | iff  : Formula V TA PA → Formula V TA PA → Formula V TA PA
  | neg  : Formula V TA PA → Formula V TA PA

def Formula.bound (nm : V) : Formula V TA PA → Prop
  | .exis n' v
  | .univ n' v => n' = nm ∨ v.bound nm

  | .pred _ _ => False
  | .neg v => v.bound nm

  | .disj a b
  | .conj a b
  | .imp a b
  | .iff a b => a.bound nm ∨ b.bound nm

def Formula.bound.dec [DecidableEq V] (nm : V) (form : Formula V TA PA) : (Decidable (bound nm form)) :=
  match form with
  | .exis n' v
  | .univ n' v =>
    if h : n' = nm then
      .isTrue (by simp only [bound, h, true_or])
    else
      match dec nm v with
      | .isTrue v => .isTrue (by simp only [bound, v, or_true])
      | .isFalse v => .isFalse (by simp only [bound, h, v, or_self, not_false_eq_true])

  | .pred _ _ => .isFalse (by simp only [bound, not_false_eq_true])
  | .neg v => dec nm v

  | .disj a b
  | .conj a b
  | .imp a b
  | .iff a b =>
    match dec nm a with
    | .isTrue p => .isTrue (by simp only [bound, p, true_or])
    | .isFalse p => match dec nm b with
      | .isTrue  p' => .isTrue (by simp only [bound, p', or_true])
      | .isFalse p' => .isFalse (by simp only [bound, p, p', or_self, not_false_eq_true])

instance [DecidableEq V] {nm : V} : Decidable (Formula.bound nm form) := Formula.bound.dec nm form

structure Interpretation (TA : TNm → Nat) (PA : PNm → Nat) :=
  dom : Type

  funcs : (nm : TNm) → Vec dom (TA nm) → dom
  preds : (nm : PNm) → Vec dom (PA nm) → Prop

-- It does not make sense to talk about a valuation without an Interpretation so we inherit
structure Valuation (V : Type) (TA : TNm → Nat) (PA : PNm → Nat) extends Interpretation TA PA :=
  vm : V → dom

def Valuation.eval (v : Valuation V TA PA) : Term V TA → v.dom
  | .var var => v.vm var
  | .const nm args =>
      v.funcs nm (mapper args)
    where
      mapper {n} : Vec (Term V TA) n → Vec v.dom n
        | .nil => .nil
        | hd %:: tl => v.eval hd %:: mapper tl

def Valuation.assign [DecidableEq V] (v : Valuation V TA PA) (n : V) (val : v.dom) : Valuation V TA PA :=
  { v with vm := fun n' => (if n' = n then val else v.vm n') }


-- Definition 7, This is in the text such a joke as they define the logic in a
-- higher logic. To continue this i will rename the function to what it is.
def Formula.denote [DecidableEq V] (v : Valuation V TA PA) : Formula V TA PA → Prop
  -- The additional definition of equality is an unnecacarry addition and should
  -- be ensured by the user
  | .pred p args => v.preds p $ args.map v.eval

  | .neg x => ¬x.denote v

  | .disj a b => a.denote v ∧ b.denote v
  | .conj a b => a.denote v ∨ b.denote v

  | .iff a b => a.denote v ↔ b.denote v
  | .imp a b => a.denote v → b.denote v

  | .exis n b => ∃ x, b.denote $ v.assign n x
  | .univ n b => ∀ x, b.denote $ v.assign n x

def Formula.denote_indep [DecidableEq V] (v : Interpretation TA PA) (form : Formula V TA PA ) : Prop :=
  ∀ vm, form.denote ⟨v, vm⟩

-- True but non-computable due to choice
theorem imp_eq_not_or : (a → b) ↔ (¬a ∨ b) := ⟨
  fun f => Classical.byContradiction
    (let ⟨nna, nb⟩ := not_or.mp ·
    nb (f $ Classical.not_not.mp nna)),
  fun | .inl na, a => (na a).elim | .inr b, _ => b⟩

namespace Exs

namespace Ex11

abbrev equalityDomain.t : Type 1 := Interpretation (fun _ : Empty => 0) (fun _ : Unit => 2)
abbrev equalityDomain.Form (V : Type) : Type := Formula V (fun _ : Empty => 0) (fun _ : Unit => 2)
def equalityDomain (dom : Type) : equalityDomain.t :=
  {
    dom,
    funcs := fun f _ => f.elim
    preds := fun | _, %[a, b] => a = b
  }

def quantAndBlock (n : Nat) : equalityDomain.Form Nat :=
  let n := n.pred
  quant (allNeq n (n.pred)) n
where
  quant inp : _ → _
    | 0   => .exis 0 inp
    | n+1 => .exis (n+1) $ quant inp n

  allNeq : _ → _ → _
    | 0,   _ => .pred .unit $ %[.var 0, .var 0] -- how to encode true
    | n, k+1 => .conj (.neg $ .pred .unit $ %[.var n, .var (k+1)]) (allNeq n k)
    | n+2, 0 => .conj (.neg $ .pred .unit $ %[.var (n+2), .var 0]) $ allNeq (n+1) n
    | 1,   0 => (.neg $ .pred .unit $ %[.var 1, .var 0])

open Formula Term PUnit in
/--
info: exis 2
  (exis 1
    (exis 0
      ((pred unit (var 2 %:: var 1 %:: %[])).neg.conj
        ((pred unit (var 2 %:: var 0 %:: %[])).neg.conj (pred unit (var 1 %:: var 0 %:: %[])).neg))))
-/
#guard_msgs in #reduce quantAndBlock 3

-- The theorem to prove the domain has to be greater than a given size is quite straight forward

end Ex11

namespace Ex12

section

variable (R : A → A → Prop)

def AxR : Prop := ∀ {x}, R x x
def AxS : Prop := ∀ {x y}, R x y → R y x
def AxT : Prop := ∀ {x y z}, R x y → R y z → R x z

end

def F : A → A → Prop := λ _ _ ↦ False

theorem F.AxR [h : Inhabited A] : ¬AxR (A := A) F := fun x => x (x := h.default)
theorem F.AxS : AxS (A := A) F := fun r => r.elim
theorem F.AxT : AxT (A := A) F := fun r => r.elim

def T : A → A → Prop := λ _ _ ↦ True

theorem T.AxR : AxR (A := A) T := .intro
theorem T.AxS : AxS (A := A) T := fun _ => .intro
theorem T.AxT : AxT (A := A) T := fun _ _ => .intro

theorem Eq.AxR : AxR (A := A) (· = ·) := by intro x; rfl
theorem Eq.AxS : AxS (A := A) (· = ·) := fun r => by subst r; rfl
theorem Eq.AxT : AxT (A := A) (· = ·) := fun a b => by subst a b; rfl

-- Just skip to the end of this section its so much work -----------------------
section SumEven
def Even (x : Nat) : Prop := ∃ v, v + v = x
def Odd  (x : Nat) : Prop := ∃ v, v + v + 1 = x

theorem Even_Odd_succ : Even x ↔ Odd x.succ :=
  ⟨fun ⟨w, v⟩ => ⟨w, v.rec rfl⟩, fun ⟨w, v⟩ => ⟨w, (Nat.succ.injEq _ _).mp v⟩⟩

theorem Odd_Even_succ : Odd x ↔ Even x.succ :=
  ⟨fun ⟨w, v⟩ => ⟨w + 1, by omega⟩, fun ⟨w, v⟩ => ⟨w - 1, (Nat.succ.injEq _ _).mp (v.rec (by omega))⟩⟩

mutual
def Even.d : (x : Nat) → Decidable (Even x)
  | 0 => .isTrue ⟨0, rfl⟩
  | n+1 => match Odd.d n with
    | .isTrue  p => .isTrue (Odd_Even_succ.mp p)
    | .isFalse p => .isFalse (p ∘ Odd_Even_succ.mpr)
def Odd.d : (x : Nat) → Decidable (Odd x)
  | 0 => .isFalse fun ⟨_, p⟩ => Nat.noConfusion p
  | n+1 => match Even.d n with
    | .isTrue p => .isTrue (Even_Odd_succ.mp p)
    | .isFalse p => .isFalse (p ∘ Even_Odd_succ.mpr)
end

def either_Even_Odd (n : Nat) : Even n ∨ Odd n :=
  match n with
  | 0   => .inl ⟨0, rfl⟩
  | n+1 => match either_Even_Odd n with
    | .inl p => .inr (Even_Odd_succ.mp p)
    | .inr p => .inl (Odd_Even_succ.mp p)

instance : Decidable (Even n) := Even.d n
instance : Decidable (Odd  n) :=  Odd.d n

theorem Even_iff_notEven_succ : Even x ↔ ¬Even x.succ := ⟨by
  intro ⟨w, p⟩
  simp only [Even, Nat.succ_eq_add_one, not_exists]
  intro _
  rw [← p]
  omega,
  fun he =>
    Even_Odd_succ.mpr $ Classical.byContradiction fun ho =>
    match either_Even_Odd x.succ with
    | .inl x => he x
    | .inr x => ho x⟩

theorem Odd_iff_notOdd_succ : Odd x ↔ ¬Odd x.succ := ⟨by
  intro ⟨w, p⟩
  simp only [Odd, Nat.succ_eq_add_one, not_exists]
  intro _
  rw [← p]
  omega,
  fun ho =>
    Odd_Even_succ.mpr $ Classical.byContradiction fun he =>
    match either_Even_Odd x.succ with
    | .inl x => he x
    | .inr x => ho x⟩

theorem Odd_iff_notEven : Odd x ↔ ¬Even x := by
  calc
    _ ↔ _ := Odd_iff_notOdd_succ
    _ ↔ _ := by rw [Even_Odd_succ]
theorem Even_iff_notOdd : Even x ↔ ¬Odd x := by
  calc
    _ ↔ _ := Even_iff_notEven_succ
    _ ↔ _ := by rw [Odd_Even_succ]

def SumEven (a b : Nat) : Prop := Even (a + b)

theorem SumEven_same_sign (h : SumEven a b) : (Even a ∧ Even b) ∨ (Odd a ∧ Odd b) :=
  match either_Even_Odd a, either_Even_Odd b with
  | .inr pa, .inr pb | .inl pa, .inl pb => by simp only [pa, pb, and_self, or_true, true_or]
  | .inr ⟨wa, pa⟩, .inl ⟨wb, pb⟩ | .inl ⟨wa, pa⟩, .inr ⟨wb, pb⟩ => by
    rcases h with ⟨w, p⟩
    omega -- exfalso

theorem SumEven.AxR : AxR SumEven := ⟨_, rfl⟩
theorem SumEven.AxS : AxS SumEven := fun ⟨w, p⟩ => ⟨w, p.rec (by omega)⟩
theorem SumEven.AxT : AxT SumEven := fun s1 s2 => by
  rcases SumEven_same_sign s1 with (⟨ex1,ey1⟩|⟨ex1,ey1⟩)
  <;> rcases SumEven_same_sign s2 with (⟨ex2,ey2⟩|⟨ex2,ey2⟩)
  <;> (try { simp_all only [Odd_iff_notEven, not_true_eq_false]; done })
  · rcases ex1 with ⟨w1, p1⟩
    rcases ey2 with ⟨w2, p2⟩
    exact ⟨w1 + w2, by omega⟩
  · rcases ex1 with ⟨w1, p1⟩
    rcases ey2 with ⟨w2, p2⟩
    exact ⟨w1 + w2 + 1, by omega⟩
end SumEven
-- Continue from here ----------------------------------------------------------

def SumEqHundred (a b : Nat) : Prop := a + b = 100

theorem SumEqHundred.AxR : ¬AxR SumEqHundred := fun h => Nat.noConfusion $ h (x := 0)
theorem SumEqHundred.AxS : AxS SumEqHundred := fun v => by dsimp [SumEqHundred] at *; omega
theorem SumEqHundred.AxT : ¬AxT SumEqHundred := fun h => Nat.noConfusion $ h (x := 0) (y := 100) (z := 0) rfl rfl

-- Just defined here to make it more transparet for supervisions
def leDef (a b : Nat) : Prop := ∃ c, a + c = b

theorem Le.AxR : AxR leDef := ⟨0, rfl⟩
theorem Le.AxS : ¬AxS leDef := (have ⟨_, p⟩ := · (⟨1, rfl⟩ : leDef 0 1); by omega)
theorem Le.AxT : AxT leDef := fun ⟨w1, p1⟩ ⟨w2, p2⟩ => ⟨w1 + w2, by omega⟩

end Ex12

-- TODO: Ex13

end Exs

