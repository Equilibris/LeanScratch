import LeanScratch.LogicProof.PropLogic.Formula
import LeanScratch.LogicProof.PropLogic.DenseFormula
import LeanScratch.LogicProof.PropLogic.Clause
import LeanScratch.LogicProof.PropLogic.SAT.DPLL
import LeanScratch.LogicProof.PropLogic.Sequent
import LeanScratch.Fin2

namespace PLogic.Exs

def Ex6_1 : Sequent [.neg $ .neg v] [v] := .negL $ .negR $ .triv
def Ex6_2 : Sequent [.conj a b] [.conj b a] :=
  .conjL $ .conjR (.cycleL .triv) .triv
def Ex6_3 : Sequent [.disj a b] [.disj b a] :=
  .disjR $ .disjL (.cycleR .triv) .triv

def Ex7_1 : Sequent [.conj (.conj a b) c] [.conj a (.conj b c)] :=
  .conjL $ .conjL $
    .conjR .triv $ .wL $ .conjR .triv $ .wL .triv

def Ex7_2 : Sequent [.conj (.disj a b) (.disj a c)] [.disj a (.conj b c)] :=
  .conjL $ .disjR $ .disjL .triv $ .cycleL $ .disjL .triv $
    .cycleR $ .conjR (.cycleL .triv) .triv

def Ex7_3 : Sequent [.neg (.disj a b)] [.conj (.neg a) (.neg b)] :=
  .negL $ .disjR $ .cycleR $ .cycleR $ .conjR
    (.negR .triv) (.negR $ .cycleR .triv)

-- Ex. falso
def Ex9_1 : Sequent [] [.imp (.conj a (.neg a)) b] :=
  .impR $ .conjL $ .cycleL $ .negL .triv


-- This shows that even though my solution is provably correct its completely
-- unsuable without filtering.
abbrev InTextEx1 : Formula (Fin 2) := .iff (.iff (.atom ⟨0, by omega⟩) (.atom ⟨1, by omega⟩)) (.iff (.atom ⟨1, by omega⟩) (.atom ⟨0, by omega⟩))
#eval (InTextEx1.transform .false).toClauseSet |> Clause.setRemoveTauto

end Exs


