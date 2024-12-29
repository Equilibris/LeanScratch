import LeanScratch.Vec
import LeanScratch.LogicProof.FirstOrderLogic.Formula

namespace FOL

structure Interpretation (TA : TNm → Nat) (PA : PNm → Nat) :=
  dom : Type

  funcs : (nm : TNm) → Vec dom (TA nm) → dom
  preds : (nm : PNm) → Vec dom (PA nm) → Prop

-- It does not make sense to talk about a valuation without an Interpretation so we inherit
structure Valuation (TA : TNm → Nat) (PA : PNm → Nat) extends Interpretation TA PA :=
  vm : Nat → dom

def Valuation.eval (v : Valuation TA PA) : Term TA → v.dom
  | .var var => v.vm var
  | .const nm args =>
      v.funcs nm (mapper args)
    where
      mapper {n} : Vec (Term TA) n → Vec v.dom n
        | .nil => .nil
        | hd %:: tl => v.eval hd %:: mapper tl

def Valuation.replace (v : Valuation TA PA) (n : Nat) (val : v.dom) : Valuation TA PA :=
  { v with vm := fun n' => (if n' = n then val else v.vm n') }

def Valuation.insert (v : Valuation TA PA) (val : v.dom) : Valuation TA PA :=
  { v with vm := fun | 0 => val | n+1 => v.vm n }


-- Definition 7, This is in the text such a joke as they define the logic in a
-- higher logic. To continue this i will rename the function to what it is.
def Formula.denote (v : Valuation TA PA) : Formula TA PA → Prop
  -- The additional definition of equality is an unnecacarry addition and should
  -- be ensured by the user
  | .pred p args => v.preds p $ args.map v.eval

  | .neg x => ¬x.denote v

  | .disj a b => a.denote v ∧ b.denote v
  | .conj a b => a.denote v ∨ b.denote v

  | .iff a b => a.denote v ↔ b.denote v
  | .imp a b => a.denote v → b.denote v

  | .exis b => ∃ x, b.denote $ v.insert x
  | .univ b => ∀ x, b.denote $ v.insert x

def Formula.denote_indep (v : Interpretation TA PA) (form : Formula TA PA) : Prop :=
  ∀ vm, form.denote ⟨v, vm⟩

