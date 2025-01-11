import LeanScratch.LogicProof.PropLogic.Clause
import LeanScratch.LogicProof.PropLogic.ClauseSet
import LeanScratch.LogicProof.PropLogic.Sat.Fup
import LeanScratch.LogicProof.PropLogic.Sat.RemoveTauto
import LeanScratch.LogicProof.PropLogic.Sat.Unit
import LeanScratch.LogicProof.PropLogic.Sat.Elim
import LeanScratch.ListUtils

namespace PLogic

variable {α : Type} [DecidableEq α]

/- 
  To implement more inteligent heuristics like backjumping, this monovariant
  wont work. For this it might be worth coming up with a notion of
  'spesificity' and 'generality', spesificity can be a non-computable
  amount of values of the domain α^n that hold. For example [] and
  [False] have a spesificities |α|^n and 0 respectively. Generality is
  the opposite of this. It is how many values a domain does not hold for,
  these are flipped of the example just given. These two will now be taken
  as a whole in forming the monovariant. This is done as if the expression
  is true spesificity will always decrease, if it is false generality will
  always increase. This is a much MUCH harder property to prove things about
  but could possibly be done using the 'fup' or similar constructions. I
  also note that 'generality' will have to be thought about a bit more as
  if an expression is false then it will already not hold for any values
  so this might have to be slgihtly reformulated.

  For now, since we're not using backjumping, 'size' is a very good
  monovariant.
-/

def fffun : α → Prop := fun _ => False
instance : Decidable (fffun x) := .isFalse False.elim

inductive DpllResult (cs : ClauseSet α)
  | holds ls (v : cs.holds (fup fffun ls))
  | fails (v : ∀ base, ¬cs.holds base)

-- Currently im skipping pure literals as theres already so much pain here lol
def dpll (cs : ClauseSet α) : DpllResult cs :=
  if h : [] = cs then
    .holds [] $ h.rec (fun _ h => ((List.mem_nil_iff _).mp h).elim)
    -- Order has to be a bit messed up due to how easy certian theorems are to prove
  else if hContra : cs.ContainsContra then
    .fails (fun _ => ClauseSet.ContainsContra_not_holds hContra)
  else
    let csNa := cs.removeTauto
    let csEu := csNa.elimAll csNa.extractUnits

    if hSz : csEu.size < cs.size then
      match dpll csEu with
      | .holds ls p => .holds (csNa.extractUnits ++ ls) $ by
        rw [ClauseSet.elimAll.correct, fup.assoc] at p
        rwa [ClauseSet.removeTauto.correct]
      | .fails p => .fails fun base h => by
        dsimp [csEu, csNa] at p
        specialize p base
        -- TODO: reverse the arrows here to make them simplify by defualt
        rw [ClauseSet.removeTauto.correct] at h
        rw [ClauseSet.elimAll.correct, ClauseSet.extractUnits.correct h] at p
        exact p h
    else
      have : csEu.size ≤ cs.size := calc
        _ ≤ _ := ClauseSet.elimAll.size
        _ ≤ _ := ClauseSet.removeTauto.sz
      have csSzEq : csEu.size = cs.size := by omega

      let el := csEu.extract fun hSzZ => by
        have := csSzEq.symm.trans hSzZ
        cases cs
        · exact h rfl
        · clear *-hContra this
          simp only [ClauseSet.size, add_eq_zero] at this
          rcases this with ⟨pa, _⟩
          dsimp [Clause.size] at pa
          simp only [List.mem_cons, not_or] at hContra
          rcases hContra with ⟨neqEmpty, _⟩
          rename_i hd _ _ _
          rcases hd with ⟨(_|_),(_|_)⟩ <;> simp_all
      let tryA := csEu.elim el .true
      have : tryA.size < cs.size := calc
        _ < _ := ClauseSet.elim.sz_strict ClauseSet.extract.mem
        _ = _ := csSzEq

      match dpll tryA with
      | .holds ls p => .holds (csNa.extractUnits ++ [⟨el, .true⟩] ++ ls) $ by
        dsimp [tryA, csEu] at p
        rw [ClauseSet.elim.correct, fup.assoc] at p
        rw [ClauseSet.elimAll.correct, fup.assoc, ←List.append_assoc] at p
        rwa [ClauseSet.removeTauto.correct]
      | .fails pA =>
      let tryB := csEu.elim el .false
      have : tryB.size < cs.size := calc
        _ < _ := ClauseSet.elim.sz_strict ClauseSet.extract.mem
        _ = _ := csSzEq

      match dpll tryB with
      | .holds ls p => .holds (csNa.extractUnits ++ [⟨el, .false⟩] ++ ls) $ by
        rw [ClauseSet.elim.correct, fup.assoc] at p
        rw [ClauseSet.elimAll.correct, fup.assoc, ←List.append_assoc] at p
        rwa [ClauseSet.removeTauto.correct]
      | .fails pB =>
        .fails fun base h => by
          dsimp [tryA, tryB] at pA pB
          specialize pA base
          specialize pB base
          rw [ClauseSet.elim.correct, ClauseSet.elimAll.correct] at pA pB
          rcases fup.either (ClauseSet.holds · cs) h el with (h|h)
          <;> rw [ClauseSet.removeTauto.correct] at h
          · rw [ClauseSet.extractUnits.correct h] at pA
            exact pA h
          · rw [ClauseSet.extractUnits.correct h] at pB
            exact pB h
        -- this is a contra case
termination_by cs.size

-- Took some time but here we go
/-- info: 'PLogic.dpll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dpll

def DpllResult.toDecidable {cs : ClauseSet α} : DpllResult cs → Decidable (∃ base, cs.holds base)
  | .holds ls v => .isTrue ⟨fup fffun ls, v⟩
  | .fails p => .isFalse $ not_exists.mpr p

