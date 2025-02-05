import LeanScratch.LogicProof.FirstOrderLogic.Formula

-- Pathalogical example of unification algorithm f(x) ∩ f(f(x))

namespace FOL.DeBrujin

variable [DecidableEq Nm] {TA : Nm → Nat}

def Term.unify : Term TA n → Term TA n → Option (Fin n × Term TA n)
  | .var x, t | t, .var x => .some ⟨x, t⟩
  | .const x ax, .const y ay =>
    if heq : x = y then
      let ay : Vec (Term TA n) (TA x) := heq ▸ ay
      mapper ax ay
    else .none
  where
    mapper {k} : Vec (Term TA n) k → Vec (Term TA n) k → _
      | %[], %[] => .none
      | hd₁ %:: tl₁, hd₂ %:: tl₂ => hd₁.unify hd₂ <|> mapper tl₁ tl₂



