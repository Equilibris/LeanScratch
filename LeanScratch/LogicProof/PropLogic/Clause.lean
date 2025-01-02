import Mathlib.Data.List.Basic
import LeanScratch.LogicProof.PropLogic.DenseFormula

namespace PLogic

structure Clause (Atom : Type) :=
  args : List Atom
  lits : List Atom
deriving DecidableEq

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

-- [a, c →]  [→ b, c]
-- (¬a ∨ ¬c) ∧ (b ∨ c) → [a → b, a → c]

def Clause.merge : Clause Atom → Clause Atom → Clause Atom
  | ⟨a1, l1⟩, ⟨a2, l2⟩ => ⟨a1 ++ a2, l1 ++ l2⟩

-- Fuck me this theorem is truly ass to prove
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
      | h1 :: t1, [] =>
        have := sol t1 ba [] bl
        by
        simp_all only [denote.conjoin, List.append_eq, List.nil_append, and_imp, imp_iff_not_or,
          denote.disjoin, imp_false, not_and, eq_iff_iff]
        constructor
        · rintro (h|h|h|h)   <;> simp_all
        · rintro ((h|h)|h|h) <;> simp_all
      | [], h1 :: t1 => 
        have := sol [] ba t1 bl
        by
        simp_all only [List.nil_append, imp_iff_not_or, denote.conjoin, true_implies, eq_iff_iff,
          denote.disjoin, List.append_eq, denote.disjoin_append]
        constructor
        · rintro (h|h|h|h)
          <;> simp_all
        · rintro ((h|(h|h))|h|h)
          <;> simp_all
      | h1 :: t1, h2 :: t2  => 
        have := sol t1 ba t2 bl
        by
        simp_all only [denote.conjoin_append, denote.disjoin_append, and_imp, imp_iff_not_or,
          eq_iff_iff, denote.conjoin, List.append_eq, denote.disjoin]
        constructor
        · rintro (h|h|h|h|h|h) <;> simp_all
        · rintro ((h|h|h|h)|h|h) <;> simp_all

def Formula.Dense.toClauseSet : Dense Atom → List (Clause Atom)
  | .atom v => [{ args := [], lits := [v] }]
  | .negAtom v => [{ args := [v], lits := [] }]
  | .conj a b => a.toClauseSet ++ b.toClauseSet
  | .disj a b => a.toClauseSet.bind (b.toClauseSet.map $ ·.merge)

def Clause.setHolds base (set : List (Clause Atom)) :=
  ∀ x ∈ set, x.denote base

def Formula.Dense.toClauseSet.correct (form : Dense Atom)
    : form.denote base = Clause.setHolds base form.toClauseSet :=
  match form with
  | .negAtom v | .atom v => by
    simp only [denote, Clause.setHolds, toClauseSet, List.mem_singleton, Clause.denote, forall_eq,
      Clause.denote.conjoin, and_true, Clause.denote.disjoin, imp_false, or_false, true_implies]
  | .disj a b => by
    simp [denote, correct a, correct b, toClauseSet, Clause.setHolds, ]
    constructor
    · rintro (h|h) _ x1 amem x2 bmem rfl
      <;> rw [Clause.merge_denote]
      · exact .inl $ h x1 amem
      · exact .inr $ h x2 bmem
    · rintro h
      rw [forall_or_left.symm, ]
      intro x1
      rw [forall_or_right.symm]
      intro x2
      rw [forall_or_left.symm]
      intro bmem
      rw [forall_or_right.symm]
      intro amem
      exact Clause.merge_denote.mp $ h (x2.merge x1) _ amem _ bmem rfl
  | .conj a b => by
    simp only [denote, Clause.setHolds, toClauseSet, correct a, correct b, forall_and.symm]
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

/--
info: 'PLogic.Formula.Dense.toClauseSet.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Formula.Dense.toClauseSet.correct

