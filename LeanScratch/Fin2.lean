import Mathlib.Data.Fin.Fin2
import Mathlib.Util.WhatsNew

instance Fin2.decEq : DecidableEq (Fin2 n) := fun
  | .fz, .fs _ | .fs _, .fz => .isFalse Fin2.noConfusion
  | .fz, .fz => .isTrue rfl
  | .fs a, .fs b => match decEq a b with
    | .isTrue p => .isTrue $ p.rec rfl
    | .isFalse p => .isFalse (p ∘ (Fin2.fs.injEq _ _).mp)

