import LeanScratch.Vec

namespace FOL

inductive Term {Nm : Type} (Arity : Nm → Nat)
  | const (nm : Nm) (app : Vec (Term Arity) (Arity nm))

inductive Formula {TNm PNm : Type} (TA : TNm → Nat) (PA : PNm → Nat) 
  | pred (nm : PNm) (app : Vec (Term TA) (PA nm)) : Formula TA PA 

  -- We use non-parametric HOS to get around substitution issues
  | univ : (Term TA → Formula TA PA) → Formula TA PA 
  | exis : (Term TA → Formula TA PA) → Formula TA PA 

  | conj : Formula TA PA → Formula TA PA → Formula TA PA 
  | disj : Formula TA PA → Formula TA PA → Formula TA PA 
  | imp  : Formula TA PA → Formula TA PA → Formula TA PA 
  | iff  : Formula TA PA → Formula TA PA → Formula TA PA 
  | neg  : Formula TA PA → Formula TA PA

