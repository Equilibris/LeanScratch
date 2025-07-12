import LeanScratch.Semantics.PCF.Red
import LeanScratch.Computation.GRFs

namespace PCF

def GRFType : Nat → Ty
  | 0 => .nat
  | n+1 => .arrow .nat $ GRFType n

-- TODO
def translate : Comp.GRFunStx Unit n → Expr
  | .comp _ _ => sorry
  | .mini _ _ => sorry
  | .succ => sorry
  | .zero => sorry
  | .proj _ => sorry
  | .nRec _ _ => sorry
