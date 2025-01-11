import Mathlib.Data.List.Basic
import LeanScratch.LogicProof.PropLogic.Clause

namespace PLogic

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

@[simp]
theorem ClauseSet.mem_cons : ClauseSet.mem a (hd :: tl) = (a ∈ hd ∨ ClauseSet.mem a tl) := by
  simp only [mem, List.mem_cons, exists_eq_or_imp]

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

def ClauseSet.size : ClauseSet α → Nat
  | [] => 0
  | hd :: tl => hd.size + ClauseSet.size tl

def ClauseSet.extract (c : ClauseSet α) (hSz : c.size ≠ 0) : α := match c with
  | [] => (hSz rfl).elim
  | hd :: tl =>
    if hHdSz : hd.size ≠ 0 then hd.extract hHdSz
    else
      have := not_not.mp hHdSz
      ClauseSet.extract tl $ by
        simp only [size, this, Nat.zero_add] at hSz
        exact hSz

theorem ClauseSet.extract.mem {cs : ClauseSet α} {p} : cs.mem $ cs.extract p :=
  match cs with
  | [] => (p rfl).elim
  | hd :: tl => by
    set x := extract _ p with h
    apply mem_cons.mpr
    dsimp [extract] at h
    split at h <;> rw [h]
    · exact .inl Clause.extract.mem
    · exact .inr extract.mem

abbrev ClauseSet.ContainsContra (cs : ClauseSet α) : Prop := ⟨[], []⟩ ∈ cs
instance {cs : ClauseSet α} [DecidableEq α] : Decidable cs.ContainsContra :=
  if h : ⟨[], []⟩ ∈ cs then .isTrue h else .isFalse h

theorem ClauseSet.ContainsContra_not_holds
    {cs : ClauseSet α} (h : cs.ContainsContra)
    : ¬cs.holds base := not_forall.mpr ⟨⟨[], []⟩, (· h .intro)⟩
