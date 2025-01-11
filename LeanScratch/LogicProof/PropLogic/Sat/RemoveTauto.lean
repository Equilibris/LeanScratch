import LeanScratch.LogicProof.PropLogic.ClauseSet

namespace PLogic

variable {α : Type} [DecidableEq α]

def ClauseSet.removeTauto (inp : ClauseSet α) : ClauseSet α :=
  inp.filter (¬·.isTauto)

theorem ClauseSet.removeTauto.correct {cs : ClauseSet α} : cs.holds base = cs.removeTauto.holds base :=
  match cs with
  | [] => rfl
  | hd :: tl =>
    have := ClauseSet.removeTauto.correct (base := base) (cs := tl)
    by
    dsimp only [holds] at this
    by_cases h : hd.isTauto
    <;> simp_all [holds, this, removeTauto, h, Clause.isTauto_denote]

def ClauseSet.removeTauto.sz {s : ClauseSet α} : s.removeTauto.size ≤ s.size :=
  match s with
  | [] => Nat.zero_le _
  | hd :: tl =>
    have := ClauseSet.removeTauto.sz
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
