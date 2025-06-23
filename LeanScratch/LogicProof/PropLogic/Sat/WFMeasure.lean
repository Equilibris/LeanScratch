import LeanScratch.LogicProof.PropLogic.Clause
import LeanScratch.LogicProof.PropLogic.ClauseSet
import LeanScratch.LogicProof.PropLogic.Sat.Fup
import LeanScratch.LogicProof.PropLogic.Sat.RemoveTauto
import LeanScratch.LogicProof.PropLogic.Sat.Unit
import LeanScratch.LogicProof.PropLogic.Sat.Elim
import LeanScratch.ListUtils

namespace PLogic.ClauseSet

def R (a b : ClauseSet α) := ∀ base,
     (a.holds base → b.holds base)
  ∧ ¬(b.holds base → a.holds base)

namespace R

instance : Trans (R (α := α)) R R where
  trans a b base :=
    have ⟨al, ar⟩ := a base
    have ⟨bl, br⟩ := b base
    ⟨bl ∘ al, by tauto⟩ -- could just have well all have been a tauto




