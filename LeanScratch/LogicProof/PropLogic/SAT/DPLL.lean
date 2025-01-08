import LeanScratch.LogicProof.PropLogic.Clause
import LeanScratch.ListUtils

namespace PLogic

variable {α : Type} [DecidableEq α]

def Clause.size : Clause α → Nat | ⟨a, l⟩ => a.length + l.length

def ClauseSet.size : ClauseSet α → Nat
  | [] => 0
  | hd :: tl => hd.size + ClauseSet.size tl

def ClauseSet.removeTauto (inp : ClauseSet α) : ClauseSet α :=
  inp.filter (¬·.isTauto)

theorem ClauseSet.holds.invar_remoteTauto (s : ClauseSet α) : s.holds base = s.removeTauto.holds base :=
  match s with
  | [] => rfl
  | hd :: tl =>
    have := invar_remoteTauto (base := base) tl
    by
    dsimp only [holds] at this
    by_cases h : hd.isTauto
    <;> simp_all [holds, this, removeTauto, h, Clause.isTauto_denote]

def ClauseSet.size.decreases_removeTauto (s : ClauseSet α) : s.removeTauto.size ≤ s.size :=
  match s with
  | [] => Nat.zero_le _
  | hd :: tl =>
    have := decreases_removeTauto tl
    by
    by_cases h : hd.isTauto
    · simp only [removeTauto, decide_not, h, decide_True, Bool.not_true, Bool.false_eq_true,
        not_false_eq_true, List.filter_cons_of_neg, size]
      simp only [removeTauto, decide_not] at this
      calc
        _ ≤ _ := this
        _ ≤ _ := Nat.le_add_left (size tl) hd.size
    · simp only [removeTauto, decide_not, h, decide_False, Bool.not_false, List.filter_cons_of_pos,
        size, Nat.add_le_add_iff_left]
      simp only [removeTauto, decide_not] at this
      exact this

def Clause.contains (v : α) : Bool → Clause α → Prop
  | .true,  ⟨a, _⟩ => v ∈ a
  | .false, ⟨_, l⟩ => v ∈ l

instance {v : α} : Decidable (Clause.contains v b c) :=
  match b, c with
  | .true,  ⟨a, _⟩ => if h : v ∈ a then .isTrue h else .isFalse h
  | .false, ⟨_, l⟩ => if h : v ∈ l then .isTrue h else .isFalse h

theorem Clause.contains_denote {c : Clause α} (h : if b then ¬base v else base v) (hC : c.contains v b) : c.denote base :=
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

def Clause.remove (v : α) : Bool → Clause α → Clause α
  | .false, ⟨a, l⟩ => ⟨a.filter (· ≠ v), l⟩
  | .true,  ⟨a, l⟩ => ⟨a, l.filter (· ≠ v)⟩

def Clause.remove_size {c : Clause α} : (c.remove v b).size ≤ c.size :=
  match b with | .true | .false => by simp [remove, size, List.filter_length_le_length]

theorem Clause.remove_denote {c : Clause α} (h : if b then ¬base v else base v)
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

def ClauseSet.elim (v : α) (b : Bool) (cs : ClauseSet α) : ClauseSet α :=
  cs.filter (¬·.contains v b) |>.map (Clause.remove v b)

theorem ClauseSet.elim_holds
    (hB : if b then ¬base v else base v) (cs : ClauseSet α)
    : cs.holds base = (cs.elim v b).holds base :=
  match cs with
  | [] => rfl
  | hd :: tl =>
    have := elim_holds hB tl
    by
    simp only [holds, eq_iff_iff] at this
    by_cases h : hd.contains v b
    <;> simp only [holds, List.mem_cons, forall_eq_or_imp, this, elim,
          decide_not, List.mem_map, forall_exists_index, and_imp, decide_True,
          Bool.not_true, Bool.false_eq_true, not_false_eq_true,
          List.filter_cons_of_neg, eq_iff_iff, and_iff_right_iff_imp,
          forall_apply_eq_imp_iff₂, (Clause.remove_denote hB).symm, h,
          decide_False, Bool.not_false, List.filter_cons_of_pos, List.map_cons]
    exact fun _ => Clause.contains_denote hB h

theorem ClauseSet.size.decreases_elim (cs : ClauseSet α) : (cs.elim v b).size ≤ cs.size :=
  match cs with
  | [] => Nat.zero_le _
  | hd :: tl => calc
      _ ≤ (hd.remove v b).size + (elim v b tl).size := by by_cases h : hd.contains v b <;> 
          simp only [elim, List.filter, h, not_true_eq_false, decide_False,
            decide_not, le_add_iff_nonneg_left, zero_le, not_false_eq_true,
            decide_True, List.map_cons, size, le_refl]
      _ ≤ hd.size + (elim v b tl).size              := Nat.add_le_add_right Clause.remove_size _
      _ ≤ hd.size + ClauseSet.size tl               := Nat.add_le_add_left (decreases_elim tl) _

theorem ClauseSet.size.decreases_elim_strict
    (cs : ClauseSet α) (hMem : cs.mem v)
    : (cs.elim v b).size < cs.size :=
  match cs with
  | [] => by rcases hMem with ⟨_, v, _⟩; exact ((List.mem_nil_iff _).mp v).elim
  | hd :: tl => by
    rcases hMem with ⟨w, wMemFull, memW⟩
    rcases List.mem_cons.mp wMemFull with (rfl | wMemTl)
    · have := decreases_elim (v := v) (b := b) tl
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
        _ ≤ hd.size + (elim v b tl).size              := Nat.add_le_add_right Clause.remove_size _
        _ < hd.size + _                               := Nat.add_lt_add_left (decreases_elim_strict tl ⟨w, wMemTl, memW⟩) _
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

abbrev ClauseSet.ContainsContra (cs : ClauseSet α) : Prop := ⟨[], []⟩ ∈ cs
instance {cs : ClauseSet α} : Decidable cs.ContainsContra :=
  if h : ⟨[], []⟩ ∈ cs then .isTrue h else .isFalse h

theorem ClauseSet.ContainsContra_not_holds
    {cs : ClauseSet α} (h : cs.ContainsContra)
    : ¬cs.holds base := not_forall.mpr ⟨⟨[], []⟩, (· h .intro)⟩

def Clause.unitize : Clause α → Option (α × Bool)
  | ⟨[x], []⟩ => .some ⟨x, .true⟩
  | ⟨[], [x]⟩ => .some ⟨x, .false⟩
  | _ => .none

theorem Clause.unitize.correct {c : Clause α} (h : c.unitize = .some ⟨x, b⟩)
    : c.denote base = if b then ¬base x else base x := by
  simp [unitize] at h
  split at h
  case h_3 => exact Option.noConfusion h
  all_goals obtain ⟨rfl, rfl⟩ := (Option.some.injEq _ _).mp h
  all_goals simp [denote, denote.conjoin, denote.disjoin]

def ClauseSet.extractUnits : ClauseSet α → List (α × Bool) := List.filterMap Clause.unitize
def ClauseSet.getUnit : ClauseSet α → Option (α × Bool)
  | [] => .none
  | hd :: tl =>
    match hd.unitize with
    | .none => ClauseSet.getUnit tl
    | .some v => .some v

def fup (base : α → Prop) (ls : List (α × Bool)) (x : α) : Prop :=
  match ls with
  | [] => base x
  | ⟨hd, .true⟩  :: tl => if x = hd then False else fup base tl x
  | ⟨hd, .false⟩ :: tl => if x = hd then True  else fup base tl x

theorem fup.assoc {base : α → Prop} : fup (fup base l1) l2 = fup base (l2 ++ l1) :=
  match l2 with
  | [] => rfl
  | ⟨hd, .false⟩ :: tl
  | ⟨hd, .true⟩ :: tl => by
    ext x
    by_cases h : x = hd
    <;> simp only [fup, h, ↓reduceIte, List.append_eq]
    exact iff_eq_eq.mpr $ Function.funext_iff.mp fup.assoc x

def fup.dec
    {base : α → Prop}
    ls
    (h : Decidable (base x)) : Decidable (fup base ls x) :=
  match ls with
  | [] => h
  | ⟨hd, .true⟩ :: tl =>
    if hEq : x = hd then
      .isFalse (by simp only [hEq, fup, ↓reduceIte, not_false_eq_true])
    else
      match fup.dec tl h with
      | .isTrue p => .isTrue (by simp only [fup, hEq, ↓reduceIte, p])
      | .isFalse p => .isFalse (by simp only [fup, hEq, ↓reduceIte, p, not_false_eq_true])
  | ⟨hd, .false⟩ :: tl => 
    if hEq : x = hd then
      .isTrue (by simp only [hEq, fup, ↓reduceIte, not_false_eq_true])
    else
      match fup.dec tl h with
      | .isTrue p => .isTrue (by simp only [fup, hEq, ↓reduceIte, p])
      | .isFalse p => .isFalse (by simp only [fup, hEq, ↓reduceIte, p, not_false_eq_true])

theorem ClauseSet.extractUnits_fup_force
    {base : α → Prop} (h : holds base cs)
    : base = fup base cs.extractUnits :=
  match cs with
  | [] => rfl
  | hd :: tl => by
    rcases ClauseSet.holds_cons.mp h with ⟨hCurr, ih⟩
    clear h
    dsimp [extractUnits, List.filterMap_cons]
    have := ClauseSet.extractUnits_fup_force ih
    split
    · exact this
    next heq =>
      simp [Clause.unitize] at heq
      split at heq
      case h_3 => exact Option.noConfusion heq
      all_goals obtain ⟨rfl, rfl⟩ := (Option.some.injEq _ _).mpr heq
      all_goals ext x
      all_goals simp only [Clause.denote, Clause.denote.conjoin, and_true,
        Clause.denote.disjoin, imp_false, fup, if_false_left, extractUnits,
        Clause.denote.conjoin, or_false, true_implies, fup, if_true_left] at hCurr this ⊢
      all_goals rw [←this]
      all_goals constructor
      all_goals by_contra!
      all_goals simp only [ne_eq, imp_iff_or_not,
        and_imp, imp_self, implies_true,
        Decidable.not_not, not_or] at this
      · rcases this with ⟨h1, h2|rfl⟩
        exact h2 h1
        exact hCurr h1
      · rcases this with ⟨⟨_, h1⟩, h2⟩
        exact h2 h1
      · rcases this with ⟨h1, _, h2⟩
        exact h2 h1
      · rcases this with ⟨(h1|rfl), h2⟩
        exact h2 h1
        exact h2 hCurr

theorem ClauseSet.units_hold_left {base : α → Prop} (h : holds base cs)
    : holds (fup base cs.extractUnits) cs := by
  rw [←ClauseSet.extractUnits_fup_force h]
  exact h

-- False, as cs.extractUnits can correct the function to match the clauses
theorem ClauseSet.units_hold {base : α → Prop}
    (h : holds (fup base cs.extractUnits) cs)
    : holds base cs :=
  match cs with
  | [] => h
  | hd :: tl => by
    simp only [extractUnits, List.filterMap_cons] at h
    split at h
    <;> rename_i heq
    · 
      sorry
    · simp only [Clause.unitize] at heq
      split at heq
      case h_3 => exact Option.noConfusion heq
      all_goals obtain ⟨rfl, rfl⟩ := (Option.some.injEq _ _).mpr heq
      all_goals simp_all only [holds_cons, Clause.denote,
        Clause.denote.conjoin, Clause.denote.disjoin, and_true, imp_false,
        or_false, true_implies, fup, ↓reduceIte, not_false_eq_true,
        if_false_left, true_and, if_true_left, not_true_eq_false, false_and,
        not_false_eq_true, true_and, false_implies, true_and]
      sorry
      sorry

/- theorem ClauseSet.units_hold {base : α → Prop} -/
/-     : holds base cs = holds (fup base cs.extractUnits) cs := -/
/-   match cs with -/
/-   | [] => rfl -/
/-   | hd :: tl => -/
/-     have := units_hold (base := base) (cs := tl) -/
/-     by -/
/-     simp only [extractUnits, List.filterMap_cons, ClauseSet.holds_cons] -/
/-     split -/
/-     · change _ = (_ ∧ holds (fup base (extractUnits tl)) tl) -/
/-       rw [this] -/
/-       simp only [eq_iff_iff, and_congr_left_iff] -/
/-       intro ha -/
/-       change _ ↔ hd.denote (fup base (ClauseSet.extractUnits tl)) -/
/-       rw [←ClauseSet.extractUnits_fup_force (this.mpr ha)] -/
/-     next heq => -/
/-       simp [Clause.unitize] at heq -/
/-       split at heq -/
/-       case h_3 => sorry -/
/-       all_goals obtain ⟨rfl, rfl⟩ := (Option.some.injEq _ _).mpr heq -/
/-       all_goals simp [Clause.denote, Clause.denote.conjoin, Clause.denote.disjoin, fup] -/
/-       sorry -/
/-       sorry -/

def ClauseSet.elimUnits (cs : ClauseSet α) : ClauseSet α :=
  cs.extractUnits.foldl (fun acc ⟨a, b⟩ => acc.elim a b) cs

def ClauseSet.elim_single_unit {cs : ClauseSet α} (h : .some ⟨v, b⟩ = cs.getUnit)
  : cs.holds (fup base [⟨v, b⟩]) = (cs.elim v b).holds base := sorry

-- This is false due to cool things with logic and stuff
/- def ClauseSet.elimUnits.correct -/
/-     {cs : ClauseSet α} -/
/-     : cs.holds (fup base cs.extractUnits) = cs.elimUnits.holds base := -/
/-   p cs.extractUnits (fun _ => id) rfl -/
/-   where -/
/-     p {cs'} (l : List (α × Bool)) (h : ∀ x ∈ l, x ∈ cs.extractUnits) -/
/-       (hCs' : holds base cs = holds base cs') -/
/-       : holds base cs = holds (fup base cs.extractUnits) (List.foldl (fun acc ⟨a, b⟩ => elim a b acc) cs' l) := -/
/-       match l with -/
/-       | [] => sorry -- hCs' -/
/-       | hd :: tl => by -/
/-         rw [List.foldl_cons, p tl (h · ∘ List.mem_cons.mpr ∘ .inr) _] -/
/-         rcases hd with ⟨a, (_|_)⟩ -/
/-         <;> simp only [ClauseSet.holds_cons] -/
/-         · sorry -/
/-         · sorry -/

/-
def ClauseSet.elimUnits (cs : ClauseSet α)
    : (x : ClauseSet α) ×' cs.holds base = x.holds base :=
  let units := cs.extractUnits
  mapper cs sorry units extractUnits.correct
  where
    mapper
        cs' (holdsDown : cs.holds base = cs'.holds base) v (sl : ∀ x ∈ v, x.size = 1)
        : (x : _) ×' cs'.holds base = x.holds base :=
      match v with
      | [] => ⟨cs', rfl⟩
      | ⟨[], [v]⟩ :: tl =>
        let ⟨cs', p⟩ := mapper (cs'.elim v .false) (by rw [ClauseSet.elim_holds _ _]) tl (by simp_all)
        ⟨cs', sorry⟩
      | ⟨[v], []⟩ :: tl =>
        let ⟨cs', p⟩ := mapper (cs'.elim v .true) sorry tl (by simp_all)
        ⟨cs', sorry⟩
      | ⟨_ :: _ :: _, _⟩ :: tl
      | ⟨_, _ :: _ :: _⟩ :: tl
      | ⟨_ :: _, _ :: _⟩ :: tl
      | ⟨[], []⟩ :: tl => by
        all_goals simp only [List.mem_cons, Clause.size, forall_eq_or_imp, List.length_nil,
          add_zero, zero_ne_one, false_and, List.length_cons] at sl
        all_goals omega
-/

inductive DpllResult (cs : ClauseSet α)
  | holds base (dec : ∀ atom, Decidable (base atom)) (v : cs.holds base)
  | fails (v : ∀ base, ¬cs.holds base)

theorem dpll.elimUnits_preserves_contra
    (cs : ClauseSet α) (base : α → Prop) (h : ¬ClauseSet.holds base cs.elimUnits) : ¬ClauseSet.holds base cs :=
  match cs with
  | [] => h
  | hd :: tl => by
    simp only [ClauseSet.holds_cons, not_and]
    intro hHolds
    simp [ClauseSet.elimUnits, List.foldl_cons, ClauseSet.extractUnits, List.filterMap_cons] at h
    split at h
    · sorry
    · sorry

-- Currently im skipping pure literals as theres already so much pain here lol
def dpll
    (cs : ClauseSet α) (inBase : α → Prop)
    (dec : ∀ atom, Decidable (inBase atom))
    : DpllResult cs :=
  if h : [] = cs then
    .holds inBase dec $ h.rec (fun _ h => ((List.mem_nil_iff _).mp h).elim)
    -- Order has to be a bit messed up due to how easy certian theorems are to prove
  else if hContra : cs.ContainsContra then
    .fails (fun _ => ClauseSet.ContainsContra_not_holds hContra)
  else
    let csNa := cs.removeTauto
    let csEU := csNa.elimUnits
    if h : csEU.size < cs.size then
      match dpll csEU (fup inBase csNa.extractUnits) (fup.dec csNa.extractUnits $ dec ·) with
      | .holds base dec v => sorry
      | .fails p          => sorry
    else
      sorry
    /- if hContra : csEU.ContainsContra then -/
    /-   have : ∀ base, _ := fun b => ClauseSet.ContainsContra_not_holds (base := b) hContra -/
    /-   .fails $ by -/
    /-     intro base -/
    /-     specialize this base -/
    /-     clear *-this -/
    /-     change ¬cs.removeTauto.elimUnits.holds base at this -/
    /-     extract_goal -/
    /-     sorry -/
    /- else -/
    /-   sorry -/
termination_by cs.size

