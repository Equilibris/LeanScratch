import LeanScratch.LogicProof.FirstOrderLogic.Formula
import LeanScratch.LogicProof.FirstOrderLogic.Valuation
import LeanScratch.LogicProof.FirstOrderLogic.Sequent

namespace FOL.Exs

namespace Ex11

abbrev equalityDomain.t : Type 1 := Interpretation (fun _ : Empty => 0) (fun _ : Unit => 2)
abbrev equalityDomain.Form : Type := Formula (fun _ : Empty => 0) (fun _ : Unit => 2)
def equalityDomain (dom : Type) : equalityDomain.t :=
  {
    dom,
    funcs := fun f _ => f.elim
    preds := fun | _, %[a, b] => a = b
  }

/- def quantAndBlock (n : Nat) : equalityDomain.Form := -/
/-   let n := n.pred -/
/-   quant (allNeq n (n.pred)) n -/
/- where -/
/-   quant inp : _ → _ -/
/-     | 0   => .exis inp -/
/-     | n+1 => .exis $ quant inp n -/

/-   allNeq : _ → _ → _ -/
/-     | 0,   _ => .pred .unit $ %[.var 0, .var 0] -- how to encode true -/
/-     | n, k+1 => .conj (.neg $ .pred .unit $ %[.var n, .var (k+1)]) (allNeq n k) -/
/-     | n+2, 0 => .conj (.neg $ .pred .unit $ %[.var (n+2), .var 0]) $ allNeq (n+1) n -/
/-     | 1,   0 => (.neg $ .pred .unit $ %[.var 1, .var 0]) -/

/- open Formula Term PUnit in -/
/- /-- -/
/- info: ((pred unit (var 2 %:: var 1 %:: %[])).neg.conj -/
/-         ((pred unit (var 2 %:: var 0 %:: %[])).neg.conj (pred unit (var 1 %:: var 0 %:: %[])).neg)).exis.exis.exis -/
/- -/ -/
/- #guard_msgs in #reduce quantAndBlock 3 -/

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

def Example9 {P : Term TA → Formula TA PA} : Sequent [.univ λ x => (.conj (P x) Q) ] [.univ λ x => P x] :=
  .univR λ x => .univL x $ .conjL .triv

def Example10 {B : Term TA → Formula TA PA} : Sequent [.univ λ x => .imp A (B x)] [.imp A (.univ B)] :=
  .impR $ .univR λ x => .cycleL $ .univL x $ .impL .triv .triv

-- TODO: Ex 14, this is trivially a bunch of calls to `rw`
-- TODO: Ex 15, these are also trivial

def Ex16 {Q : Term TA → Formula TA PA} a b : Sequent [] [.neg $ .univ fun y => (.conj (.disj (Q a) (Q b)) (.neg $ Q y))] :=
  .negR $ .cL $ .univL a $ .cycleL $ .univL b
    $ .conjL $ .cycleL $ .negL $ .cycleL $ .cycleL $ .conjL $ .cycleL $
      .negL $ .disjL .triv $ .cycleR .triv

namespace Ex17
variable {P : Term TA → Formula TA PA} {Q : Term TA → Formula TA PA} {a : Term TA} {f : Term TA → Term TA}

def pa : Sequent [.conj (.univ P) (.univ Q)] [.univ fun y => .conj (P y) (Q y)] :=
  .conjL $ .univR fun x => .conjR (.univL x .triv) $ .cycleL $ .univL x .triv

def pb : Sequent [.univ fun y => .conj (P y) (Q y)] [.conj (.univ P) (.univ Q)] :=
  .conjR (.univR fun x => .univL x $ .conjL .triv) (.univR fun x => .univL x $ .conjL $ .cycleL .triv)

-- This feels like black magic due to how clean HOAS lets one implement this
def pc : Sequent [.univ fun x => .imp (P x) (P (f x)), P a] [P (f (f a))] :=
  .cL $ .univL a $ .cycleL $ .univL (f a) $ .impL (.cycleL $ .impL .triv .triv) .triv
end Ex17

-- TODO: Ex 18

namespace Ex19
variable {P : Term TA → Formula TA PA} {Q : Term TA → Formula TA PA}
         {a b : Term TA} {f : Term TA → Term TA}

def pa : Sequent [.disj (P a) (.exis (P ∘ f))] [.exis P] := 
  .disjL (.exisR a .triv) (.exisL λ y => .exisR (f y) .triv)

def pb : Sequent [.exis λ v => .disj (P v) (Q v)] [.exis P, .exis Q] :=
  .exisL λ v => .disjL (.exisR v .triv) $ .wR (.exisR v .triv)

-- Took me some time to get this as I really annoyingly think very
-- constructively. Would be nice to talk about this in a supo
def pc : Sequent [] [.exis λ z => .imp (P z) (.conj (P a) (P b))] :=
  .cR $ .exisR b $ .impR $ .wR $ .exisR a $ .impR $ .conjR .triv $ .wL .triv

end Ex19
