import Mathlib.Data.Nat.PSub
import Mathlib.Data.Rel
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Util.WhatsNew
import LeanScratch.ListUtils
import LeanScratch.Rel2

theorem List.getElem_ne_cons {tl : List α} (h : (hd :: tl)[(hd :: tl).length.pred]? ≠ .some x)
    : tl[tl.length.pred]? ≠ .some x :=
  match repl : tl with
  | [] => by simp only [length_nil, Nat.pred_eq_sub_one, zero_le, tsub_eq_zero_of_le, getElem?_nil, ne_eq,
      not_false_eq_true]
  | hd' :: tl' => by
    rw [←repl, Nat.pred_eq_sub_one] at h ⊢
    have : 1 ≤ tl.length := by
      rw [repl, length_cons, le_add_iff_nonneg_left]
      apply Nat.zero_le

    rw [length_cons, Nat.add_sub_cancel] at h
    simp (config := { singlePass := .true }) only [
        ←Nat.sub_add_cancel this, List.getElem?_cons_succ] at h
    exact h

/-- A polynomial in ω, least sig first -/
def PolyOrd := { x : List Nat // x[x.length.pred]? ≠ some 0}

namespace PolyOrd

def shift (a : PolyOrd) : PolyOrd :=
  let ⟨w, p⟩ := a
  if wNEmp : w = [] then ⟨[], by decide⟩ else
  ⟨0 :: w, by
      intro h
      cases w
      · contradiction
      case cons hd tl =>
      simp_all only [List.length_cons, Nat.pred_succ, lt_add_iff_pos_right, zero_lt_one,
        List.getElem?_eq_getElem, ne_eq, Option.some.injEq, not_false_eq_true,
        List.getElem_cons_succ]
  ⟩

private def add.inner : List ℕ → List ℕ → List ℕ
  | [], a | a, [] => a
  | hd₁::tl₁, hd₂::tl₂ => (hd₁ + hd₂) :: inner tl₁ tl₂

private lemma add.proof.inner_length a b
    : ((add.inner a b).length = a.length) ∨ ((add.inner a b).length = b.length) :=
  match a, b with
  | [], b => by
    simp only [inner, List.length_nil, List.length_eq_zero, or_true]
  | a, [] => by
    unfold add.inner
    split
    · exact Or.inr rfl
    · simp only [List.length_nil, List.length_eq_zero, true_or]
    · contradiction
  | hd₁::tl₁, hd₂::tl₂ => by
    simp only [inner, List.length_cons, add_left_inj]
    exact add.proof.inner_length _ _

theorem add.proof
  (wa : pa[pa.length.pred]? ≠ some 0)
  (wb : pb[pb.length.pred]? ≠ some 0) :
  (PolyOrd.add.inner pa pb)[(PolyOrd.add.inner pa pb).length.pred]? ≠ some 0 :=
  match pa, pb with
  | [], a => by
    simp only [add.inner, Nat.pred_eq_sub_one, ne_eq]
    exact wb
  | a, [] => by
    unfold add.inner
    intro h
    split at h <;> contradiction
  | hd₁::tl₁, hd₂::tl₂ => by
    have wa := List.getElem_ne_cons wa
    have wb := List.getElem_ne_cons wb
    simp only [inner, List.length_cons, lt_add_iff_pos_right, zero_lt_one, Option.some.injEq, Nat.pred_succ]
    intro h
    match p₁ : tl₁, p₂ : tl₂ with
    | [], [] =>
      simp_all only [List.length_singleton, Nat.pred_succ, zero_lt_one, List.getElem?_eq_getElem,
        List.getElem_cons_zero, ne_eq, Option.some.injEq, inner, List.length_nil, add_eq_zero]
    | [], hd::tl | hd::tl, [] =>
      simp_all only [List.length_singleton, Nat.pred_succ, zero_lt_one, List.getElem?_eq_getElem,
        List.getElem_cons_zero, ne_eq, Option.some.injEq, List.length_cons, lt_add_iff_pos_right,
        List.getElem_cons_succ, inner]
    | hd'₁::tl'₁, hd'₂::tl'₂ =>
      simp only [← p₁, ← p₂, List.length_cons, Nat.pred_succ, lt_add_iff_pos_right, zero_lt_one,
        Option.some.injEq
        ] at h wa wb
      have lx : 1 ≤ (add.inner tl₁ tl₂).length := by
        rcases add.proof.inner_length tl₁ tl₂ with (h|h)
        · rw [h, p₁]
          exact Nat.zero_lt_succ _
        · rw [h, p₂]
          exact Nat.zero_lt_succ _
      simp (config := { singlePass := .true }) only [
        ←Nat.sub_add_cancel lx,
        List.getElem?_cons_succ
        ] at h wa wb
      exact add.proof wa wb h

abbrev zero : PolyOrd := ⟨[], by
  simp only [List.length_nil, Nat.pred_eq_sub_one, zero_le, tsub_eq_zero_of_le, List.getElem?_nil,
    ne_eq, not_false_eq_true]⟩

def add (a : PolyOrd) (b : PolyOrd) : PolyOrd :=
    have ⟨pa, wa⟩:= a
    have ⟨pb, wb⟩:= b
    ⟨add.inner pa pb, add.proof wa wb⟩

@[simp]
theorem add_inner_zero : add.inner a [] = a := by
  induction a <;> simp only [add.inner]
@[simp]
theorem zero_add_inner : add.inner [] a = a := by
  induction a <;> simp only [add.inner]

@[simp]
theorem add_zero {a : PolyOrd} : add a zero = a := by
  rcases a with ⟨w, p⟩
  simp only [add, zero, Nat.pred_eq_sub_one, ne_eq, add_inner_zero]

@[simp]
theorem zero_add {a : PolyOrd} : add zero a = a := by
  rcases a with ⟨w, p⟩
  simp only [add, zero, Nat.pred_eq_sub_one, ne_eq, zero_add_inner]

theorem add_inner_comm : add.inner a b = add.inner b a := by
  induction a, b using add.inner.induct
  <;> simp only [add.inner, Nat.add_comm, List.cons.injEq, true_and, add_inner_zero]
  assumption

theorem add_comm {a b : PolyOrd} : add a b = add b a := by
  rcases a with ⟨a, pa⟩
  rcases b with ⟨b, pb⟩
  simp only [add, Nat.pred_eq_sub_one, ne_eq, add_inner_comm]

theorem add_inner_assoc : add.inner (add.inner a b) c = add.inner a (add.inner b c) := match a, b, c with
  | [], b, c => by repeat rw [zero_add_inner]
  | a, [], c => by rw [add_inner_zero, zero_add_inner]
  | a, b, [] => by repeat rw [add_inner_zero]
  | ha :: ta, hb :: tb, hc :: tc => by
    dsimp only [add.inner]
    rw [Nat.add_assoc, add_inner_assoc]

theorem add_assoc : add (add a b) c = add a (add b c) := by
  rcases a with ⟨a, _⟩
  rcases b with ⟨b, _⟩
  rcases c with ⟨c, _⟩
  dsimp only [add]
  congr 1
  exact add_inner_assoc

def degDec : PolyOrd → PolyOrd
  | ⟨_ :: tl, p⟩ => ⟨tl, List.getElem_ne_cons p⟩
  | x@⟨[], _⟩ => x
def tCoef : PolyOrd → ℕ
  | ⟨hd :: _, _⟩ => hd
  | ⟨[], _⟩ => 0

theorem degDec_lCoef_ext (hTc : tCoef a = tCoef b) (hDegDec : degDec a = degDec b) : a = b :=
  match a, b with
  | ⟨[], _⟩, ⟨[], _⟩ => rfl
  | ⟨hd :: tl, p⟩, ⟨[], _⟩ => by
    obtain rfl : tl = [] := (exists_subtype_mk_eq_iff.mp ⟨_, hDegDec.symm⟩).symm
    simp only [List.length_singleton, Nat.pred_succ, zero_lt_one, List.getElem?_eq_getElem,
      List.getElem_cons_zero, ne_eq, Option.some.injEq, tCoef] at p hTc
    exfalso
    exact p hTc
  | ⟨[], _⟩, ⟨hd :: tl, p⟩ => by
    obtain rfl : tl = [] := (exists_subtype_mk_eq_iff.mp ⟨_, hDegDec⟩).symm
    simp only [List.length_singleton, Nat.pred_succ, zero_lt_one, List.getElem?_eq_getElem,
      List.getElem_cons_zero, ne_eq, Option.some.injEq, tCoef] at p hTc
    exfalso
    exact p hTc.symm
  | ⟨ha :: ta, a₁⟩, ⟨hb :: tb, b₁⟩ => by
    dsimp only [degDec] at hDegDec
    obtain rfl : ta = tb := (exists_subtype_mk_eq_iff.mp ⟨_, hDegDec⟩)
    dsimp only [tCoef] at hTc
    subst hTc
    rfl

/- inductive Plt : PolyOrd → PolyOrd → Prop := -/
/-   | zeroBot : t₁.length < t₂.length → Plt ⟨t₁, p₁⟩ ⟨t₂, p₂⟩ -/
/-   | congr : tCoef a < tCoef b → degDec a = degDec b → Plt a b -/

/- theorem Plt.cons_cons (h : ha < hb) : Plt ⟨ha :: tl, pa⟩ ⟨hb :: tl, pb⟩ := .congr (by dsimp only [tCoef] ; exact h) (by simp [degDec]) -/

/- theorem Plt.antirefl : ¬Plt a a := fun h => match h with -/
/-   | .congr a _ => (lt_self_iff_false _).mp a -/
/-   | .zeroBot h => (lt_self_iff_false _).mp h -/
/- theorem Plt.not_Plt_zero : ¬Plt a zero := fun h => match h with | .congr a _ => by simp only [tCoef, zero, not_lt_zero'] at a -/

/- theorem Plt.length_le (h : Plt a b) : a.val.length ≤ b.val.length := -/
/-   match a, b, h with -/
/-   | ⟨[], _⟩, _, _ => by simp -/
/-   | _, ⟨[], _⟩, h => by -/
/-     exfalso -/
/-     exact Plt.not_Plt_zero h -/
/-   | ⟨ha :: ta, pa⟩, ⟨hb :: tb, pb⟩, .zeroBot h => by -/
/-     simp only [List.length_cons, add_lt_add_iff_right, add_le_add_iff_right] at h ⊢ -/
/-     exact Nat.le_of_succ_le h -/
/-   | ⟨ha :: ta, pa⟩, ⟨hb :: tb, pb⟩, .congr hTc hDeg => by -/
/-     simp only [degDec, Nat.pred_eq_sub_one, ne_eq] at hDeg -/
/-     obtain rfl : ta = tb := (exists_subtype_mk_eq_iff.mp ⟨_, hDeg⟩) -/
/-     simp only [List.length_cons, le_refl] -/

example : WellFounded Nat.lt := by
  apply WellFounded.intro
  intro n
  induction n
  case zero =>
    apply Acc.intro 0
    intro _ h
    contradiction
  case succ n ih =>
    apply Acc.intro (Nat.succ n)
    intro m h
    have : m = n ∨ m < n := Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ h)
    match this with
    | .inl e => rwa [e]
    | .inr e => exact Acc.inv ih e

/- theorem Plt.WF.p.zero : Acc Plt zero := .intro _ (by -/
/-   intro y h -/
/-   exact (Plt.not_Plt_zero h).elim) -/

/- theorem Plt.WF.p a : Acc Plt a := by -/
/-   rcases a with ⟨wa, pa⟩ -/
/-   induction wa -/
/-   case nil => exact Plt.WF.p.zero -/
/-   case cons hd tl ih => -/
/-     apply Acc.intro _ -/
/-     intro m h -/
/-     sorry -/

  /- match hv : a with -/
  /- | ⟨[], p⟩ => Plt.WF.p.zero -/
  /- | ⟨hd :: tl, p⟩ => .intro _ (by -/
  /-   intro y h -/
  /-   sorry -/
  /-   /- cases h -/ -/
  /-   /- exact Plt.WF.p.zero -/ -/
  /-   /- next hTc hDegDec => -/ -/
  /-   /- match y with -/ -/
  /-   /- | ⟨[], _⟩ => exact Plt.WF.p.zero -/ -/
  /-   /- | ⟨hd' :: tl', hy⟩ => -/ -/
  /-   /- simp only [degDec, Nat.pred_eq_sub_one, ne_eq] at hDegDec -/ -/
  /-   /- obtain rfl : tl = tl' := (exists_subtype_mk_eq_iff.mp ⟨_, hDegDec⟩).symm -/ -/
  /-   /- /- have : sizeOf (hd' :: tl) < sizeOf _ := sorry -/ -/ -/
  /-   /- exact Plt.WF.p _ -/ -/
  /- ) -/
/- termination_by sizeOf a.val -/
/- decreasing_by -/
/- · simp_wf -/
/-   simp only [tCoef] at hTc -/
/-   simp_all -/
/-   sorry -/

/- theorem Plt.WF.p : Acc Plt a := by -/
/-   rcases a with ⟨a, pa⟩ -/
/-   induction a; exact Plt.WF.p.zero -/
/-   case cons hd tl ih => -/
/-   constructor -/
/-   intro y h -/
/-   cases h -/
/-   exact Plt.WF.p.zero -/
/-   next hTc hDegDec => -/
/-   match y with -/
/-   | ⟨[], _⟩ => exact Plt.WF.p.zero -/
/-   | ⟨hd' :: tl', hy⟩ => -/
/-   simp only [degDec, Nat.pred_eq_sub_one, ne_eq, tCoef] at hDegDec hTc -/
/-   obtain rfl : tl = tl' := (exists_subtype_mk_eq_iff.mp ⟨_, hDegDec⟩).symm -/
/-   clear hDegDec -/
/-   sorry -/
/- theorem Plt.WF : WellFounded Plt := by -/
/-   constructor -/
/-   sorry -/


/- inductive inner.plt' : List ℕ → List ℕ → Prop -/
/-   | longer : plt' [] (hd :: tl) -/
/-   | congr {hd₁ hd₂ tl₁ tl₂} : plt' tl₁ tl₂ → plt' (hd₁ :: tl₁) (hd₂ :: tl₂) -/
/-   | inc : plt' (hd :: tl) (hd.succ :: tl) -/

inductive inner.plt : List ℕ → List ℕ → Prop
  | longer : plt [] (hd :: tl)
  | congr {hd₁ hd₂ tl₁ tl₂} : plt tl₁ tl₂ → plt (hd₁ :: tl₁) (hd₂ :: tl₂)
  | inc : hd₁ < hd₂ → plt (hd₁ :: tl) (hd₂ :: tl)

/- theorem innerEqs : inner.plt = Relation.TransGen inner.plt' := by -/
/-   ext a b -/
/-   constructor -/
/-   <;> intro h -/
/-   <;> induction h -/
/-   next hd tl => exact .single .longer -/
/-   next hd₁ hd₂ tl₁ tl₂ h ih => -/
/-     have : Relation.TransGen inner.plt' (hd₁ :: tl₁) (hd₁ :: tl₂) := Relation.transGenMap (.congr ·) ih -/
/-     apply Relation.TransGen.tail this -/
/-     sorry -/
/-     /- induction ih -/ -/
/-     /- next ih => exact .single $ .congr ih -/ -/
/-     /- · sorry -/ -/
/-     /- exact .single sorry -/ -/
/-   next hd₁ hd₂ tl h => -/
/-     sorry -/
/-   next h => -/
/-     induction h -/
/-     case longer => exact .longer -/
/-     case congr ih => exact .congr ih -/
/-     case inc ih => exact .inc (Nat.lt_add_one _) -/
/-   next cont h ih => -/
/-     sorry -/

theorem inner.plt.len (h : inner.plt a b) : a.length ≤ b.length := by
  induction h
  · simp only [List.length_nil, List.length_cons, le_add_iff_nonneg_left, zero_le]
  · simp_all only [List.length_cons, add_le_add_iff_right]
  · simp only [List.length_cons, le_refl]

def plt : PolyOrd → PolyOrd → Prop | ⟨l₁, _⟩, ⟨l₂, _⟩ => inner.plt l₁ l₂

theorem plt.WF.acc.z : Acc plt ⟨[], p⟩ := .intro _ (by
  rintro ⟨y, py⟩ h
  dsimp only [plt] at h
  cases h)

inductive succR : ℕ → ℕ → Prop | succ : succR n (n + 1)

example : n < k ↔ (Relation.TransGen succR) n k := by
  constructor <;> intro h
  · induction k generalizing n
    · contradiction
    next ih =>
      cases Nat.le_iff_lt_or_eq.mp $ Nat.le_of_lt_succ h
      next z =>
        specialize ih z
        exact .tail ih (.succ)
      next z =>
        rw [z]
        exact .single .succ
  · induction h
    next base =>
      cases base
      exact lt_add_one n
    next z ih =>
      cases z
      exact Nat.lt_add_right 1 ih

set_option pp.proofs true in
theorem plt.WF.acc : Acc plt a := by
  rcases a with ⟨a, pa⟩
  induction a
  · exact plt.WF.acc.z
  next hd tl ih =>
    apply Acc.intro _
    have pa' := List.getElem_ne_cons pa
    specialize ih pa'
    rintro ⟨y, py⟩ (h|h|h)
    case longer => exact plt.WF.acc.z
    case congr hd' tl' =>
      sorry
      /- have py' := List.getElem_ne_cons py -/
      /- have : Acc plt ⟨tl', py'⟩ := Acc.inv ih (by dsimp [plt]; exact h) -/
      /- apply Acc.inv sorry sorry -/
    case inc hd' =>
      have py' := List.getElem_ne_cons py
      sorry
    /- .intro _ (by -/
    /- rintro ⟨y, py⟩ (h|h|h) -/
    /- · exact plt.WF.acc.z -/
    /- case congr hd' tl' => -/
    /-   have py := List.getElem_ne_cons py -/
    /-   sorry -/
    /- case inc hd' => -/
    /-   sorry -/

/- theorem plt.WF.acc : Acc plt a := match a with -/
/-   | ⟨[], p⟩ => plt.WF.acc.z -/
/-   | ⟨hd :: tl, p⟩ => .intro _ (by -/
/-     rintro ⟨y, py⟩ (h|h|h) -/
/-     · exact plt.WF.acc.z -/
/-     case congr hd' tl' => -/
/-       have py := List.getElem_ne_cons py -/
/-       sorry -/
/-     case inc hd' => -/
/-       sorry -/
/-   ) -/

end PolyOrd


