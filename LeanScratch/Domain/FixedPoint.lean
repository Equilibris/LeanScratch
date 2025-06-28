import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import LeanScratch.Domain.Dom

namespace Dom

variable [ida : PartialOrder α]

section
class PreFixedPoint (d : α) (f : α → α) : Prop where
  fix : f d ≤ d

class LeastPreFixedPoint (lfp : α) (f : α → α) extends PreFixedPoint lfp f : Prop where
  least {d} [pfp : PreFixedPoint d f] : lfp ≤ d

def LeastPreFixedPoint.allEq
    {a b : α}
    (ha : LeastPreFixedPoint a f)
    (hb : LeastPreFixedPoint b f)
    : a = b :=
  le_antisymm
    (ha.least)
    (hb.least)

instance {f : α → α} : Subsingleton (PSigma (LeastPreFixedPoint · f)) where
  allEq a b := by
    rcases a with ⟨wa, pa⟩
    rcases b with ⟨wb, pb⟩
    obtain rfl := LeastPreFixedPoint.allEq pa pb
    rfl
end

theorem LeastPreFixedPoint.is_fixed_point
    {f : α → α} (m : Monotone f)
    [ha : LeastPreFixedPoint fixf f ]
    : f fixf = fixf :=
  ida.le_antisymm _ _
    (ha.fix)
    (ha.least (pfp := ⟨m ha.fix⟩))
section
