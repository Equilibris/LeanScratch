import LeanScratch.Vec

namespace FOL

inductive Term {Nm : Type} (Arity : Nm → Nat)
  | var   (idx : Nat) -- De Bujin index as i cant be bothered doing anything else
  | const (nm : Nm) (app : Vec (Term Arity) (Arity nm))

inductive Formula (TA : TNm → Nat) (PA : PNm → Nat)
  | pred (nm : PNm) (app : Vec (Term TA) (PA nm))

  | univ : Formula TA PA → Formula TA PA
  | exis : Formula TA PA → Formula TA PA

  | conj : Formula TA PA → Formula TA PA → Formula TA PA
  | disj : Formula TA PA → Formula TA PA → Formula TA PA
  | imp  : Formula TA PA → Formula TA PA → Formula TA PA
  | iff  : Formula TA PA → Formula TA PA → Formula TA PA
  | neg  : Formula TA PA → Formula TA PA


