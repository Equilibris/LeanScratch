import LeanScratch.Domain.PartialFunc
import LeanScratch.Domain.LeastPreFixedPoint

namespace Dom

variable [i : Dom α] {f : α → α} (m : Monotone f)

example {fixf : LeastPreFixedPoint f} : f fixf = fixf :=
  i.le_antisymm _ _
    (fixf.lfp_fix)
    (fixf.lfp_least $ m fixf.lfp_fix)
