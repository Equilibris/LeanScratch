/-
  This file has 3 main sections,

  1. #defns   where all the constructs are defined
  2. #correct where they are proven correct
  3. #size    where we state facts about their size
-/

import LeanScratch.LogicProof.PropLogic.ClauseSet
import LeanScratch.LogicProof.PropLogic.Sat.Fup
import LeanScratch.ListUtils

namespace PLogic

section

variable {α : Type} [DecidableEq α]

section defns

def Clause.contains (v : α) : Bool → Clause α → Prop
  | .true,  ⟨a, _⟩ => v ∈ a
  | .false, ⟨_, l⟩ => v ∈ l

instance {v : α} : Decidable (Clause.contains v b c) := match b, c with
  | .true,  ⟨a, _⟩ => if h : v ∈ a then .isTrue h else .isFalse h
  | .false, ⟨_, l⟩ => if h : v ∈ l then .isTrue h else .isFalse h

def Clause.remove (v : α) : Bool → Clause α → Clause α
  | .false, ⟨a, l⟩ => ⟨a.filter (· ≠ v), l⟩
  | .true,  ⟨a, l⟩ => ⟨a, l.filter (· ≠ v)⟩

def ClauseSet.elim (v : α) (b : Bool) (cs : ClauseSet α) : ClauseSet α :=
  cs.filter (¬·.contains v b) |>.map (Clause.remove v b)

def ClauseSet.elimAll (cs : ClauseSet α) : List (α × Bool) → ClauseSet α
  | [] => cs
  | ⟨v, b⟩ :: tl => (ClauseSet.elimAll (cs.elim v b) tl)

end defns

section correct

theorem Clause.contains.correct {c : Clause α} (h : if b then ¬base v else base v) (hC : c.contains v b) : c.denote base :=
  match hB : b with
  | .true => p1 hB hC
  | .false => fun _ => p2 hB hC
  where
    p1 {l} (hB : b = .true) (hContains : v ∈ l) (hC : denote.conjoin base l) :=
      match l with
      | [] => ((List.mem_nil_iff v).mp hContains).elim
      | hd :: tl => by
        simp_all only [hB]
        rcases List.mem_cons.mp hContains with (rfl|hContains)
        · exact (h hC.left).elim
        · exact p1 hB hContains hC.right
    p2 {l} (hB : b = .false) (hContains : v ∈ l) : denote.disjoin base l :=
      match l with
      | [] => ((List.mem_nil_iff v).mp hContains).elim
      | hd :: tl => by
        simp_all only [hB]
        rcases List.mem_cons.mp hContains with (rfl|hContains)
        · exact .inl h
        · exact .inr (p2 hB hContains)

theorem Clause.remove.correct {c : Clause α} (h : if b then ¬base v else base v)
    : c.denote base = (c.remove v b).denote base :=
  match hB : b with
  | .true => imp_congr_eq rfl $ p1 hB c.lits
  | .false => imp_congr_eq (p2 hB _) rfl
  where
    p1 (hB : b = .true) l2 : (denote.disjoin base l2) = (denote.disjoin base (l2.filter (· ≠ v))) :=
      match l2 with
      | [] => rfl
      | hd :: tl =>
        have := p1 hB tl
        by
        subst hB
        simp only [↓reduceIte] at h
        by_cases heq : hd = v
        · subst heq
          simp only [denote.disjoin, h, this, ne_eq, decide_not, false_or, decide_True,
            Bool.not_true, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg]
        · simp only [denote.disjoin, this, ne_eq, decide_not, List.filter, heq, not_false_eq_true,
            decide_True]
    p2 (hB : b = .false) l2 : (denote.conjoin base l2) = (denote.conjoin base (l2.filter (· ≠ v))) :=
      match l2 with
      | [] => rfl
      | hd :: tl =>
        have := p2 hB tl
        by
        subst hB
        simp only [↓reduceIte] at h
        by_cases heq : hd = v
        · subst heq
          simp only [denote.conjoin, h, this, ne_eq, decide_not, true_and, decide_True,
            Bool.not_true, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg]
        · simp only [denote.conjoin, this, ne_eq, decide_not, heq, decide_False, Bool.not_false,
            List.filter_cons_of_pos]

-- Massive theorem that was very needed
theorem ClauseSet.elim.correct
    {cs : ClauseSet α}
    :  (cs.elim v b).holds base = cs.holds (fup base [⟨v, b⟩]) :=
  match cs with
  | [] => by simp [holds, elim]
  | hd :: tl =>
    have := elim.correct (cs := tl) (v := v) (b := b) (base := base)
    by
    by_cases h' : Clause.contains v b hd
    <;> simp only [holds_cons, elim, decide_not, h',   decide_True,  Bool.not_true,
          not_false_eq_true,  List.filter_cons_of_neg, decide_False, Bool.not_false,
          Bool.false_eq_true, List.filter_cons_of_pos, List.map_cons]
    <;> simp only [this.symm, elim, decide_not, eq_iff_iff, iff_and_self, and_congr_left_iff]
    <;> intro _
    · exact clauseContains h'
    · rw [clauseRemove h']
  where
    clauseRemove {hd} (h : ¬Clause.contains v b hd) : hd.denote (fup base [(v, b)]) = (Clause.remove v b hd).denote base :=
      match b with
      | .true  => by
        dsimp [Clause.contains] at h
        dsimp [Clause.remove, Clause.denote]
        rw [clauseRemove.conjoin_nonmem h, clauseRemove.disjoinEq]
      | .false  => by
        dsimp [Clause.contains] at h
        dsimp [Clause.remove, Clause.denote]
        rw [clauseRemove.disjoin_nonmem h, clauseRemove.conjoinEq]

    clauseRemove.conjoinEq {l}
        : Clause.denote.conjoin (fup base [(v, false)]) l = Clause.denote.conjoin base (l.filter (¬· = v)) :=
      match l with
      | [] => rfl
      | hd :: tl => by
        by_cases hEq : hd = v
        · simp only [Clause.denote.conjoin, hEq, clauseRemove.conjoinEq, decide_not, decide_True,
            Bool.not_true, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, eq_iff_iff,
            and_iff_right_iff_imp]
          intro _
          simp only [fup, ↓reduceIte]
        · simp [Clause.denote.conjoin, hEq]
          rw [clauseRemove.conjoinEq]
          have : fup base [(v, false)] hd = base hd := by simp only [fup, hEq, ↓reduceIte]
          rw [this]
          simp only [decide_not]
    clauseRemove.disjoinEq {l}
        : Clause.denote.disjoin (fup base [(v, true)]) l = Clause.denote.disjoin base (l.filter (¬· = v)) :=
      match l with
      | [] => rfl
      | hd :: tl => by
        by_cases hEq : hd = v
        · simp only [Clause.denote.disjoin, hEq, clauseRemove.disjoinEq, decide_not, decide_True,
            Bool.not_true, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, eq_iff_iff,
            or_iff_right_iff_imp]
          intro h
          simp only [fup, ↓reduceIte] at h
        · simp only [Clause.denote.disjoin, decide_not, hEq, decide_False, Bool.not_false,
            List.filter_cons_of_pos]
          rw [clauseRemove.disjoinEq]
          have : fup base [(v, true)] hd = base hd := by simp only [fup, hEq, ↓reduceIte]
          rw [this]
          simp only [decide_not]

    clauseRemove.conjoin_nonmem {l b} (hNmem : v ∉ l)
        : Clause.denote.conjoin (fup base [⟨v, b⟩]) l = Clause.denote.conjoin base l :=
      match l with
      | [] => rfl
      | hd :: tl => by
        simp only [List.mem_cons, not_or] at hNmem
        rcases hNmem with ⟨neq, hNmem⟩
        simp only [Clause.denote.conjoin, clauseRemove.conjoin_nonmem hNmem, eq_iff_iff,
          and_congr_left_iff]
        intro _
        cases b
        <;> simp_all [fup]
        · exact .inl (neq ·.symm)
        · exact fun _ => (neq ·.symm)
    clauseRemove.disjoin_nonmem {l b} (hNmem : v ∉ l) 
        : Clause.denote.disjoin (fup base [⟨v, b⟩]) l = Clause.denote.disjoin base l :=
      match l with
      | [] => rfl
      | hd :: tl => by
        simp only [List.mem_cons, not_or] at hNmem
        rcases hNmem with ⟨neq, hNmem⟩
        simp only [Clause.denote.disjoin, clauseRemove.disjoin_nonmem hNmem, eq_iff_iff]
        constructor
        <;> rintro (h|triv)
        <;> (try exact .inr triv)
        <;> cases b
        <;> simp_all only [fup, if_true_left, ite_self, true_or, if_false_left, and_true]
        · exact .inl $ h (neq ·.symm)
        · exact .inl (neq ·.symm)


    clauseContains {hd} (h : Clause.contains v b hd) : hd.denote (fup base [(v, b)]) :=
      match b with
      | .true  => by
        dsimp [Clause.contains, Clause.denote] at h ⊢
        rw [imp_iff_not_or]
        exact .inl (clauseContains.pos h)
      | .false => by
        dsimp [Clause.contains, Clause.denote] at h ⊢
        intro _
        exact clauseContains.neg h

    clauseContains.pos {l} (h : v ∈ l) (conj : Clause.denote.conjoin (fup base [(v, true)]) l) : False :=
      match l with
      | [] => (List.mem_nil_iff _).mp h
      | hd :: tl => by
        have ⟨conja, conjb⟩ := (Clause.denote.conjoin_append (a := [hd])).mp conj
        rcases List.mem_cons.mp h with (rfl|h)
        · simp only [Clause.denote.conjoin, fup, ↓reduceIte, and_true] at conja
        · exact clauseContains.pos h conjb
    clauseContains.neg {l} (h : v ∈ l) : Clause.denote.disjoin (fup base [(v, false)]) l :=
      match l with
      | [] => ((List.mem_nil_iff _).mp h).elim
      | hd :: tl =>
        (Clause.denote.disjoin_append (a := [hd])).mpr $ by
        rcases List.mem_cons.mp h with (rfl|h)
        · simp only [Clause.denote.disjoin, fup, ↓reduceIte, or_false, if_true_left, true_or]
        · exact .inr $ clauseContains.neg h

theorem ClauseSet.elimAll.correct {cs : ClauseSet α} : (cs.elimAll ls).holds base = cs.holds (fup base ls)  :=
  match ls with
  | [] => rfl
  | hd :: tl => by
    dsimp [elimAll]
    change _ = holds (fup base ([hd] ++ tl)) _
    rw [←fup.assoc, ClauseSet.elim.correct.symm, ClauseSet.elimAll.correct]

end correct

section sz

theorem Clause.remove.sz {c : Clause α} : (c.remove v b).size ≤ c.size :=
  match b with | .true | .false => by simp [remove, size, List.filter_length_le_length]

theorem ClauseSet.elim.sz {cs : ClauseSet α} : (cs.elim v b).size ≤ cs.size :=
  match cs with
  | [] => Nat.zero_le _
  | hd :: tl => calc
      _ ≤ (hd.remove v b).size + (elim v b tl).size := by by_cases h : hd.contains v b <;>
          simp only [elim, List.filter, h, not_true_eq_false, decide_False,
            decide_not, le_add_iff_nonneg_left, zero_le, not_false_eq_true,
            decide_True, List.map_cons, size, le_refl]
      _ ≤ hd.size + (elim v b tl).size              := Nat.add_le_add_right Clause.remove.sz _
      _ ≤ hd.size + ClauseSet.size tl               := Nat.add_le_add_left ClauseSet.elim.sz _

theorem ClauseSet.elim.sz_strict
    {cs : ClauseSet α} (hMem : cs.mem v)
    : (cs.elim v b).size < cs.size :=
  match cs with
  | [] => by rcases hMem with ⟨_, v, _⟩; exact ((List.mem_nil_iff _).mp v).elim
  | hd :: tl => by
    rcases hMem with ⟨w, wMemFull, memW⟩
    rcases List.mem_cons.mp wMemFull with (rfl | wMemTl)
    · let this := ClauseSet.elim.sz (v := v) (b := b) (cs := tl)
      by_cases h : w.contains v b
      · simp only [elim, decide_not, h, decide_True, Bool.not_true, Bool.false_eq_true,
          not_false_eq_true, List.filter_cons_of_neg, gt_iff_lt]
        change _ + 0 < _ + _
        rw [Nat.add_comm w.size]
        simp only [elim, decide_not] at this
        apply add_lt_add_of_le_of_lt this
        simp only [Clause.mem, Membership.mem, Clause.size, add_pos_iff] at memW ⊢
        rcases memW with (h|h)
        · exact .inl $ List.length_pos_of_mem h
        · exact .inr $ List.length_pos_of_mem h
      · simp only [elim, decide_not, h, decide_False, Bool.not_false, List.filter_cons_of_pos,
          List.map_cons, size, gt_iff_lt] at this ⊢
        rw [Nat.add_comm, Nat.add_comm w.size]
        apply add_lt_add_of_le_of_lt this
        clear this wMemFull
        cases b
        <;> simp_all only [Membership.mem, Clause.mem, Clause.contains, Clause.size, Clause.remove,
          ne_eq, decide_not, add_lt_add_iff_right, or_false, false_or, add_lt_add_iff_left]
        exact memP w.args memW
        exact memP w.lits memW
    · calc
        _ ≤ (hd.remove v b).size + (elim v b tl).size := by by_cases h : hd.contains v b <;>
          simp only [elim, List.filter, h, not_true_eq_false, decide_False,
            le_add_iff_nonneg_left, zero_le, not_false_eq_true, decide_True,
            decide_not, List.map_cons, size, le_refl]
        _ ≤ hd.size + (elim v b tl).size              := Nat.add_le_add_right Clause.remove.sz _
        _ < hd.size + _                               := Nat.add_lt_add_left (ClauseSet.elim.sz_strict ⟨w, wMemTl, memW⟩) _
  where
    memP {v} (l : List α) (h : v ∈ l): (List.filter (fun x ↦ !decide (x = v)) l).length < l.length :=
      match l with
      | [] => ((List.mem_nil_iff _).mp h).elim
      | hd :: tl => by
        simp only [List.mem_cons] at h
        by_cases h' : hd = v
        · subst h'
          simp only [decide_True, Bool.not_true, Bool.false_eq_true, not_false_eq_true,
            List.filter_cons_of_neg, List.length_cons]
          apply Nat.lt_of_succ_le
          apply (add_le_add_iff_right 1).mpr
          exact List.filter_length_le_length
        · simp_all only [decide_False, Bool.not_false, List.filter_cons_of_pos, List.length_cons,
            add_lt_add_iff_right]
          rcases h with (rfl|h)
          · exact (h' rfl).elim
          exact memP tl h

theorem ClauseSet.elimAll.size {cs : ClauseSet α} : (cs.elimAll ls).size ≤ cs.size :=
  match ls with
  | [] => Nat.le_refl cs.size
  | _ :: _ => calc
      _ ≤ (elim _ _ cs).size := elimAll.size
      _ ≤ _ := ClauseSet.elim.sz

end sz
end

