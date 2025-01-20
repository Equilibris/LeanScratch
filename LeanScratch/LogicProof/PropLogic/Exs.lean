import LeanScratch.LogicProof.PropLogic.Formula
import LeanScratch.LogicProof.PropLogic.DenseFormula
import LeanScratch.LogicProof.PropLogic.Clause
import LeanScratch.LogicProof.PropLogic.Sat.DPLL
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

-- Looks like my algorithm is insanely inefficent to find these... ah well
/--
info: [{ args := [0, 0, 1], lits := [0] },
 { args := [0], lits := [0, 0, 1] },
 { args := [0, 1, 0], lits := [0] },
 { args := [0], lits := [0, 1, 0] },
 { args := [1, 0, 1], lits := [0] },
 { args := [1], lits := [0, 0, 1] },
 { args := [1, 1, 0], lits := [0] },
 { args := [1], lits := [0, 1, 0] },
 { args := [0, 0, 1], lits := [1] },
 { args := [0], lits := [1, 0, 1] },
 { args := [0, 1, 0], lits := [1] },
 { args := [0], lits := [1, 1, 0] },
 { args := [1, 0, 1], lits := [1] },
 { args := [1], lits := [1, 0, 1] },
 { args := [1, 1, 0], lits := [1] },
 { args := [1], lits := [1, 1, 0] },
 { args := [1, 0, 1], lits := [1] },
 { args := [1], lits := [1, 0, 1] },
 { args := [1, 1, 0], lits := [1] },
 { args := [1], lits := [1, 1, 0] },
 { args := [0, 0, 1], lits := [1] },
 { args := [0], lits := [1, 0, 1] },
 { args := [0, 1, 0], lits := [1] },
 { args := [0], lits := [1, 1, 0] },
 { args := [1, 0, 1], lits := [0] },
 { args := [1], lits := [0, 0, 1] },
 { args := [1, 1, 0], lits := [0] },
 { args := [1], lits := [0, 1, 0] },
 { args := [0, 0, 1], lits := [0] },
 { args := [0], lits := [0, 0, 1] },
 { args := [0, 1, 0], lits := [0] },
 { args := [0], lits := [0, 1, 0] }]
-/
#guard_msgs in
#eval InTextEx1.transform .true |>.toClauseSet

abbrev Ex20 : ClauseSet Bool := [⟨[], [.true, .false]⟩, ⟨[.true], [.false]⟩, ⟨[.false], [.true]⟩, ⟨[.true, .false], []⟩]

/-- info: PLogic.DpllResult.fails _ -/
#guard_msgs in
#eval dpll Ex20



end Exs


