import Mathlib.Order.Lattice
import LeanScratch.Domain.Lub
import LeanScratch.Domain.ChainTrellis

class Dom (α : Type _) extends PartialOrder α, OrderBot α where
  complete (c : Dom.C α) (hc : Dom.Chain c) : α
  complete_lub (c : Dom.C α) (hc : Dom.Chain c) : Dom.Lub c (complete c hc)

namespace Dom

variable [Dom α]

instance {c : C α} {hc : _} : Lub c (complete c hc) := complete_lub _ hc

def complete_bound {c : C α} {hc : _} (n : Nat) : c n ≤ complete c hc :=
  (complete_lub c hc).lub_bound n
def complete_least {c : C α} {hc : _} (x : α) : (∀ n, c n ≤ x) → complete c hc ≤ x :=
  (complete_lub c hc).lub_least x

def ChainTrellis.complete_merge
    {motive : CT α}
    (hMotive : ChainTrellis motive)
    {p2 : Chain fun n₁ ↦ complete (motive n₁) (hMotive.x n₁)}
    : complete (fun n₁ => complete (motive n₁) (hMotive.x n₁)) p2
    = complete (fun n => motive n n) hMotive.diag :=
  have hlubs := fun n => complete_lub (motive n) (hMotive.x n)
  have hxc := complete_lub _ p2
  have hDiag := complete_lub motive.diag hMotive.diag
  ChainTrellis.lubXDiag hlubs hxc hDiag

def ChainTrellis.complete_comm
    {motive : CT α}
    (hMotive : ChainTrellis motive)
    {p2 p2' : _}
    : complete (fun n₁ => complete (motive n₁) (hMotive.x n₁)) p2
    = complete (fun n₁ => complete (motive · n₁) (hMotive.y n₁)) p2' :=
  have hxlubs := fun n => complete_lub (motive n) (hMotive.x n)
  have hxc := complete_lub _ p2
  have hylubs := fun n => complete_lub (motive · n) (hMotive.y n)
  have hyc := complete_lub _ p2'
  ChainTrellis.lubCEq hxlubs hylubs hxc hyc

def CT.complete_comm
    {motive : CT α}
    (p1  : (n : Nat) → Chain (motive n ·))
    (p1' : (n : Nat) → Chain (motive · n))
    {p2 p2' : _}
    : complete (fun n₁ => complete (motive n₁) (p1 n₁)) p2
    = complete (fun n₁ => complete (motive · n₁) (p1' n₁)) p2' :=
  have hMotive : ChainTrellis motive := ⟨fun n _ _ m' hn hm =>
    le_trans ((p1  n).le_lift hm) ((p1' m').le_lift hn)⟩
  hMotive.complete_comm

def complete_mono
    [Dom α]
    {dn en : C α}
    {hd he : _}
    (h : ∀ n, dn n ≤ en n)
    : complete dn hd ≤ complete en he :=
  Lub.mono (hdlub := complete_lub _ hd) (helub := complete_lub _ he) h

def complete_const {d : α}
    : complete (fun _ => d) (⟨fun _ => le_refl _⟩) = d :=
  Lub.allEq (complete_lub _ _) (Lub.const $ fun _ => rfl)

