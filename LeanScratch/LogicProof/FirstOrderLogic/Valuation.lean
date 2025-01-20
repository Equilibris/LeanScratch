import LeanScratch.Vec
import LeanScratch.LogicProof.FirstOrderLogic.Formula

namespace FOL

structure Interpretation (TA : TNm → Nat) (PA : PNm → Nat) :=
  dom : Type

  funcs : (nm : TNm) → Vec dom (TA nm) → dom
  preds : (nm : PNm) → Vec dom (PA nm) → Prop

structure Valuation (TA : TNm → Nat) (PA : PNm → Nat) extends Interpretation TA PA

def Valuation.eval (v : Valuation TA PA) : Term TA → v.dom
  | .const nm args =>
      v.funcs nm (mapper args)
    where
      mapper {n} : Vec _ n → Vec v.dom n
        | .nil => .nil
        | hd %:: tl => v.eval hd %:: mapper tl

-- Definition 7, This is in the text such a joke as they define the logic in a
-- higher logic. To continue this i will rename the function to what it is.
def Formula.denote (v : Valuation TA PA) : Formula TA PA → Prop
  -- The additional definition of equality is an unnecacarry addition and should
  -- be ensured by the user
  | .pred p args => v.preds p $ args.map v.eval

  | .neg x => ¬x.denote v

  | .disj a b => a.denote v ∨ b.denote v
  | .conj a b => a.denote v ∧ b.denote v

  | .iff a b => a.denote v ↔ b.denote v
  | .imp a b => a.denote v → b.denote v

  | .exis b => ∃ x, (b x).denote v
  | .univ b => ∀ x, (b x).denote v

namespace DeBrujin

structure Valuation (TA : TNm → Nat) (PA : PNm → Nat) (n : Nat) extends Interpretation TA PA :=
  vs : Vec dom n

def Valuation.eval (v : Valuation TA PA n) : Term TA n → v.dom
  | .var x => v.vs.lookup $ Fin2.ofFin x
  | .const nm args =>
      v.funcs nm (mapper args)
    where
      mapper {n} : Vec _ n → Vec v.dom n
        | .nil => .nil
        | hd %:: tl => v.eval hd %:: mapper tl

def Valuation.assign (base : Valuation TA PA n) (v : base.dom) : Valuation TA PA n.succ :=
  ⟨base.toInterpretation, v %:: base.vs⟩

def Formula.denote (v : Valuation TA PA n) : Formula TA PA n → Prop
  -- The additional definition of equality is an unnecacarry addition and should
  -- be ensured by the user
  | .pred p args => v.preds p $ args.map v.eval

  | .neg x => ¬x.denote v

  | .disj a b => a.denote v ∨ b.denote v
  | .conj a b => a.denote v ∧ b.denote v

  | .iff a b => a.denote v ↔ b.denote v
  | .imp a b => a.denote v → b.denote v

  | .exis b => ∃ x, b.denote (v.assign x)
  | .univ b => ∀ x, b.denote (v.assign x)

def Term.toHoAS.correct
    {f : Term TA (0 + n)} {ls : Vec (Term TA 0) n}

    {heq : HEq ls $ ls.map (Valuation.mk interp (%[])).eval}

    : FOL.Valuation.eval ⟨interp⟩ (f.substAll ls).toHoAS
    = Valuation.eval ⟨interp, ls'⟩ f :=
  match f with
  | .var _ => by
    sorry
  | .const _ _ => sorry

def Formula.toHoAS.correct
    {f : Formula TA PA (0 + n)} {ls : Vec (Term TA 0) n}

    {heq : HEq ls $ ls.map (Valuation.mk interp (%[])).eval}

    : (f.substAll ls).toHoAS.denote ⟨interp⟩
    = f.denote ⟨interp, ls'⟩ :=
  match f with
  | .pred p args => by
    sorry

  | .neg x => sorry

  | .disj a b => sorry
  | .conj a b => sorry

  | .iff a b => sorry
  | .imp a b => sorry

  | .exis b => sorry
  | .univ b => sorry
