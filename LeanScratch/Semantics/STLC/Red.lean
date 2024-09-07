import LeanScratch.Semantics.STLC.Stx
import Mathlib.Data.Rel
import LeanScratch.Relation

namespace STLC

inductive Red : Stx → Stx → Prop
  | appl : Red a a' → Red (.app a b) (.app a' b)
  | appr : Red b b' → Red (.app a b) (.app a b')
  | beta : Red (.app (.abs _ body) v) (body.β v)

/- theorem refSet_maintain (h : Red a b) (hempty : a.refSet 0 = {}) : b.refSet 0 = {} := by -/
/-   induction h -/
/-   <;> simp_all [Stx.refSet, Nat.succ_eq_add_one, Stx.β, Stx.replace] -/
/-   <;> obtain ⟨ha, hb⟩ := Finset.union_eq_empty.mp hempty -/
/-   case appl h a_ih => -/
/-     exact Finset.union_eq_empty.mpr ⟨a_ih ha, hb⟩ -/
/-   case appr h a_ih => -/
/-     exact Finset.union_eq_empty.mpr ⟨ha, a_ih hb⟩ -/
/-   case beta x body v=> -/
/-     induction body -/
/-     <;> simp [Stx.refSet, Stx.replace, Stx.replace.bvar] -/
/-     · split <;> (try split) -/
/-       · exact hb -/
/-       · simp_all only [Stx.refSet, Nat.lt_one_iff, ite_false, Finset.union_empty, -/
/-           Finset.singleton_ne_empty] -/
/-       next h => -/
/-         simp only [not_lt, nonpos_iff_eq_zero] at h -/
/-         contradiction -/
/-     case app fn arg fn_ih arg_ih  => -/
/-       sorry -/
/-     case abs body' body_ih => -/
/-       sorry -/

abbrev RedStar := Relation.ReflTransGen Red

def Ex.fstFn (a b : Ty) : Stx := .abs a (.abs b (.bvar 1))
def Ex.sndFn (a b : Ty) : Stx := .abs a (.abs b (.bvar 0))
def Ex.id (a : Ty) : Stx := .abs a (.bvar 0)

def d0 := Ty.direct 0

example : Red (.app (Ex.id d0) (.bvar n)) (.bvar n) := .beta
example : Red (.app (Ex.id d0) z) z := by
  have x : z = Stx.β (.bvar 0) z := by simp [Stx.β, Stx.replace, Stx.replace.bvar]
  nth_rw 2 [x]
  exact .beta
example : Red (.app (Ex.sndFn d0 d0) x) (Ex.id d0) := .beta

example : RedStar (.app (.app (Ex.fstFn d0 d0 ) a) b) a := by
  have : RedStar (.app (.app (Ex.fstFn d0 d0 ) a) b) _ := .tail (.tail .refl (.appl .beta)) .beta
  simp [Stx.replace, Stx.replace.bvar] at this
  sorry
/-   calc -/
/-     RedStar _ (((Stx.abs d0 (Stx.bvar 1)).β (Stx.bvar 0)).app (Stx.bvar 1)) := .tail .refl (.appl .beta) -/
/-     RedStar _ _ := sorry -/
/- example : RedStar (.abs ) -/


