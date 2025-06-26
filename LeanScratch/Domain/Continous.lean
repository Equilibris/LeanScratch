import LeanScratch.Domain.Dom

namespace Dom

variable [dd : Dom D] [de : Dom E]

class Continous (f : D → E) where
  mono : Monotone f
  preserves_lubs (c : Chain D) : f (dd.chain_complete)
