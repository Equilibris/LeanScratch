import Mathlib.Order.Lattice
import LeanScratch.Domain.Lub
import LeanScratch.Domain.ChainTrellis

class Dom.LawfulBot (α : Type _) extends Bot α, LE α where
  bot_le (x : α) : ⊥ ≤ x

class Dom (α : Type _) extends PartialOrder α, Dom.LawfulBot α where
  complete (c : Dom.C α) (hc : Dom.Chain c) : α
  complete_lub (c : Dom.C α) (hc : Dom.Chain c) : Dom.Lub c (complete c hc)

namespace Dom

variable [Dom α]

def ChainTrellis.complete_merge
    {motive : CT α}
    (hMotive : ChainTrellis motive)
    {p1 : (n₁ : Nat) → Chain (motive n₁)}
    {p2 : Chain fun n₁ ↦ complete (motive n₁) (p1 n₁)}
    : complete (fun n₁ => complete (motive n₁) (hMotive.x n₁)) p2
    = complete (fun n => motive n n) hMotive.diag :=
  have hlubs := fun n => complete_lub (motive n) (p1 n)
  have hxc := complete_lub _ p2
  have hDiag := complete_lub motive.diag hMotive.diag
  ChainTrellis.lubXDiag hlubs hxc hDiag

def Lub.complete_const
    {d : α}
    {p : _}
    : complete (fun _ => d) p = d :=
  Lub.allEq (complete_lub _ p) (Lub.const $ fun _ => rfl)

