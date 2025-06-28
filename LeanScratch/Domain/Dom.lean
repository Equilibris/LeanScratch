import Mathlib.Order.Lattice
import LeanScratch.Domain.ChainTrellis

class Dom.LawfulBot (α : Type _) extends Bot α, LE α where
  bot_le (x : α) : ⊥ ≤ x

class Dom (α : Type _) extends PartialOrder α, Dom.LawfulBot α where
  chain_complete (c : Dom.Chain α) : Dom.Lub c

