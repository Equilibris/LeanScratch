import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import LeanScratch.Domain.Dom

namespace Dom

variable [ida : PartialOrder α]

section
def PreFixedPoint (d : α) (f : α → α) : Prop := f d ≤ d

structure LeastPreFixedPoint (f : α → α) where
  lfp       : α -- also written fix f
  lfp_fix   : PreFixedPoint lfp f
  lfp_least : PreFixedPoint d f → lfp ≤ d

instance {f : α → α} : CoeHead (LeastPreFixedPoint f) α := ⟨(·.lfp)⟩
abbrev fix (f : α → α) := LeastPreFixedPoint f

instance {f : α → α} : Subsingleton (LeastPreFixedPoint f) where
  allEq a b := by
    rcases a with ⟨a, a_fix, a_least⟩
    rcases b with ⟨b, b_fix, b_least⟩
    rw [LeastPreFixedPoint.mk.injEq]
    exact ida.le_antisymm a b
      (a_least b_fix)
      (b_least a_fix)
end

theorem LeastPreFixedPoint.is_fixed_point
    {f : α → α} (m : Monotone f)
    (fixf : LeastPreFixedPoint f)
    : f fixf = fixf :=
  ida.le_antisymm _ _
    (fixf.lfp_fix)
    (fixf.lfp_least $ m fixf.lfp_fix)

section
