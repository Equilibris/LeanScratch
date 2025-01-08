import Mathlib.Data.List.Basic
import LeanScratch.LogicProof.PropLogic.DenseFormula

namespace PLogic

structure Clause (Atom : Type) :=
  args : List Atom
  lits : List Atom
deriving DecidableEq, Repr

def Clause.mem (v : Atom) : Clause Atom → Prop
  | ⟨a, l⟩ => v ∈ a ∨ v ∈ l

instance : Membership Atom (Clause Atom) := ⟨Clause.mem⟩

instance [DecidableEq Atom] {v : Atom} : Decidable (Clause.mem v c) :=
       if ha : v ∈ c.args then .isTrue $ .inl ha
  else if hb : v ∈ c.lits then .isTrue $ .inr hb
  else .isFalse fun | .inl v => ha v | .inr v => hb v
-- Might not be needed
instance [DecidableEq Atom] {c : Clause Atom} : Decidable (v ∈ c) := instDecidableMemOfDecidableEq

def Clause.denote (c : Clause Atom) (base : Atom → Prop) : Prop :=
  conjoin c.args → disjoin c.lits
  where
    conjoin : _ → _
      | [] => True
      | hd :: tl => base hd ∧ conjoin tl
    disjoin : _ → _
      | [] => False
      | hd :: tl => base hd ∨ disjoin tl

@[simp]
def Clause.denote.disjoin_append : disjoin base (a ++ b) = (disjoin base a ∨ disjoin base b) :=
  match a with
  | [] => by simp only [List.nil_append, disjoin, false_or]
  | hd :: tl => by
    simp only [disjoin, List.append_eq _, disjoin_append (a := tl) (b := b)]
    ext
    tauto

@[simp]
def Clause.denote.conjoin_append : conjoin base (a ++ b) = (conjoin base a ∧ conjoin base b) :=
  match a with
  | [] => by simp only [List.nil_append, conjoin, true_and]
  | hd :: tl => by
    simp only [conjoin, List.append_eq _, conjoin_append (a := tl) (b := b)]
    ext
    tauto

theorem Clause.contra_Clause : ¬(Clause.mk [] []).denote base := fun h => by
  simp only [denote, denote.conjoin, denote.disjoin, imp_false, not_true_eq_false] at h

def Clause.isTauto (clause : Clause Atom) : Prop :=
  ∃ el, el ∈ clause.args ∧ el ∈ clause.lits

instance Clause.isTauto.dec [DecidableEq Atom] {clause : Clause Atom} : Decidable (Clause.isTauto clause) :=
  decLs clause.args clause.lits
  where
    decLs (l1 : List _) : (l2 : List _) → Decidable (∃ el, el ∈ l1 ∧ el ∈ l2)
      | [] => .isFalse (by simp only [List.not_mem_nil, and_false, exists_false, not_false_eq_true])
      | hd :: tl =>
        if h' : hd ∈ l1 then
          .isTrue ⟨hd, h', List.mem_cons_self hd _⟩
        else
          match decLs l1 tl with
          | .isTrue p => .isTrue (by rcases p with ⟨w, a, b⟩; exact ⟨w, a, List.mem_cons_of_mem hd b⟩)
          | .isFalse p => .isFalse (by simp_all; rintro w h rfl ; exact h' h)

def Clause.isTauto_denote {c : Clause Atom} : c.isTauto → c.denote base
  | ⟨w, pa, pb⟩ => fun x => p pa pb x
  where
    p {w : Atom} {l1 l2} (ha : w ∈ l1) (hb : w ∈ l2) (h : denote.conjoin base l1) : denote.disjoin base l2 :=
      match l1, l2 with
      | [], _ => ((List.mem_nil_iff w).mp ha).elim
      | _, [] => ((List.mem_nil_iff w).mp hb).elim
      | h1 :: t1, h2 :: t2 => by
        have ha' := ha
        have hb' := hb
        have h' := h
        simp only [List.mem_cons, denote.conjoin, denote.disjoin] at ha hb h ⊢
        rcases ha with (rfl|ha)
        <;> rcases hb with (rfl|hb)
        · exact .inl h.left
        · exact .inr $ p ha' hb h'
        · exact p ha hb' h.right
        · exact .inr $ p ha hb h.right
    termination_by l1.length + l2.length

def Clause.merge : Clause Atom → Clause Atom → Clause Atom
  | ⟨a1, l1⟩, ⟨a2, l2⟩ => ⟨a1 ++ a2, l1 ++ l2⟩

-- Fuck me this theorem is truly ass to prove
-- note to self i need to stop proof-bashing
@[simp]
theorem Clause.merge_denote {a b : Clause Atom}
    : (a.merge b).denote base = (a.denote base ∨ b.denote base) :=
  sol a.args b.args a.lits b.lits
  where
    sol (aa ba al bl : List _)
        : (denote.conjoin base (aa ++ ba) → denote.disjoin base (al ++ bl)) =
          ((denote.conjoin base aa → denote.disjoin base al) ∨
            (denote.conjoin base ba → denote.disjoin base bl)) :=
      match aa, al with
      | [], [] => by simp only [List.nil_append, eq_iff_iff, iff_or_self]; exact (contra_Clause · |>.elim)
      | h1 :: t1, other =>
        have := sol t1 ba other bl
        by
        simp_all only [denote.conjoin, List.append_eq, List.nil_append, and_imp, imp_iff_not_or,
          denote.disjoin, imp_false, not_and, eq_iff_iff]
        tauto
      | [], h1 :: t1 =>
        have := sol [] ba t1 bl
        by
        simp_all only [List.nil_append, imp_iff_not_or, denote.conjoin, true_implies, eq_iff_iff,
          denote.disjoin, List.append_eq, denote.disjoin_append]
        tauto

abbrev ClauseSet (Atom : Type) : Type := List (Clause Atom)

def ClauseSet.mem (a : Atom) (c : ClauseSet Atom) : Prop := ∃ c' ∈ c, a ∈ c'
instance [DecidableEq Atom] {a : Atom} : Decidable (ClauseSet.mem a c) :=
  p c
  where
    p : (x : List _) → Decidable (ClauseSet.mem a x)
      | [] => .isFalse (fun ⟨_, mem, _⟩ => (List.mem_nil_iff _).mp mem)
      | hd :: tl =>
        if h : a ∈ hd then .isTrue ⟨hd, ⟨List.mem_cons_self _ _, h⟩⟩ 
        else
          match p tl with
          | .isTrue p => .isTrue (by rcases p with ⟨w, a, b⟩; exact ⟨w, List.mem_cons_of_mem _ a, b⟩)
          | .isFalse p => .isFalse (by simp_all [ClauseSet.mem, h])

def Formula.Dense.toClauseSet : Dense Atom → ClauseSet Atom
  | .atom v => [{ args := [], lits := [v] }]
  | .negAtom v => [{ args := [v], lits := [] }]
  | .conj a b => a.toClauseSet ++ b.toClauseSet
  | .disj a b => a.toClauseSet.bind (b.toClauseSet.map $ ·.merge)

def ClauseSet.holds base (set : ClauseSet Atom) :=
  ∀ x ∈ set, x.denote base

-- And this is violently proof-bashed
def Formula.Dense.toClauseSet.correct (form : Dense Atom)
    : form.denote base = form.toClauseSet.holds base :=
  match form with
  | .negAtom v | .atom v => by
    simp only [denote, ClauseSet.holds, toClauseSet, List.mem_singleton, Clause.denote, forall_eq,
      Clause.denote.conjoin, and_true, Clause.denote.disjoin, imp_false, or_false, true_implies]
  | .disj a b => by
    simp only [denote, correct a, ClauseSet.holds, correct b, toClauseSet, List.mem_bind,
      List.mem_map, forall_exists_index, and_imp, eq_iff_iff]
    constructor
    · rintro (h|h) _ x1 amem x2 bmem rfl
      <;> rw [Clause.merge_denote]
      · exact .inl $ h x1 amem
      · exact .inr $ h x2 bmem
    · rintro h
      simp only [forall_or_left.symm, forall_or_right.symm]
      intro x1 bmem x2 amem
      exact Clause.merge_denote.mp $ h (x2.merge x1) _ amem _ bmem rfl
  | .conj a b => by
    simp only [denote, ClauseSet.holds, toClauseSet, correct a, correct b, forall_and.symm]
    ext
    constructor
    <;> intro h x
    <;> specialize h x
    <;> simp only [List.mem_append] at h ⊢
    · rcases h with ⟨pa, pb⟩
      rintro (x|x)
      · exact pa x
      · exact pb x
    · exact ⟨h ∘ .inl, h ∘ .inr⟩

theorem ClauseSet.holds_cons : holds base (hd :: tl) = (hd.denote base ∧ holds base tl) := by
  simp only [holds, List.mem_cons, forall_eq_or_imp]


/--
info: 'PLogic.Formula.Dense.toClauseSet.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Formula.Dense.toClauseSet.correct

