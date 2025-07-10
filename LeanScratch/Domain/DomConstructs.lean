import Mathlib.Order.Lattice
import LeanScratch.Domain.ChainTrellis
import LeanScratch.Domain.Continous

namespace Dom

variable {A B C : _} [da : Dom A] [db : Dom B] [dc : Dom C]

instance : Dom Unit where
  bot_le | .unit => le_refl _
  complete _ _ := .unit
  complete_lub _ _ := {
    lub_least := fun _ _ => le_refl _
    lub_bound := fun _ => le_refl _
  }


