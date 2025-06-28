import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import LeanScratch.Domain.Lub

namespace Dom

variable [ida : PartialOrder α]

abbrev CT (α : Type _) := Nat → Nat → α

class ChainTrellis (gen : CT α) [PartialOrder α] where
  chain (n m n' m' : Nat) : n ≤ n' → m ≤ m' → gen n m ≤ gen n' m'

variable {ct : CT α} [ hct : ChainTrellis ct ]

def CT.x (x : Nat) : C α := (fun y => ct x y)
def CT.y (y : Nat) : C α := (fun x => ct x y)

instance CT.hx (x : Nat) : Chain (ct.x x) where
  chain := fun y => hct.chain _ _ _ _ (Nat.le_refl x) (Nat.le_succ y)
instance CT.hy (y : Nat) : Chain (ct.y y) where
  chain := fun x => hct.chain _ _ _ _ (Nat.le_succ x) (Nat.le_refl y)

def ChainTrellis.xlubC [v : ChainTrellis ct]
    (lubc : C α)
    (hLubEx : ∀ n, Lub (ct.x n) (lubc n)) : Chain lubc where
  chain := fun n => by
    apply (hLubEx n).mono fun y => v.chain _ _ _ _ (Nat.le_succ n) (Nat.le_refl y)
    have ib : Lub (ct.x n.succ) (lubc n.succ) := by infer_instance
    exact ib

def ChainTrellis.ylubC [v : ChainTrellis ct]
    (lubc : C α)
    (hLubEx : ∀ n, Lub (ct.y n) (lubc n)) : Chain lubc where
  chain := fun n => by
    apply (hLubEx n).mono fun x => v.chain _ _ _ _ (Nat.le_refl x) (Nat.le_succ n)
    have ib : Lub (ct.y n.succ) (lubc n.succ) := by infer_instance
    exact ib

def CT.diag : C α := fun n => ct n n

def ChainTrellis.diag : Chain ct.diag where
  chain := fun n => hct.chain _ _ _ _ (Nat.le_succ n) (Nat.le_succ n)

def ChainTrellis.lubXDiag
    {lubxc : C α}
    (hLubEx : ∀ n, Lub (ct.x n) (lubxc n))
    (hlubx : Lub lubxc lubdx) (hlubd : Lub ct.diag lubd)
    : lubdx = lubd :=
  ida.le_antisymm _ _
    (by
      refine hlubx.lub_least lubd fun n => (hLubEx n).lub_least lubd fun n1 => ?_
      -- get the value on the diagonal
      apply ida.le_trans _ (ct (n + n1) (n + n1)) _
      exact (hct.chain _ _ _ _ (Nat.le_add_right _ _) (Nat.le_add_left _ _))
      exact (hlubd.lub_bound (n + n1)))
    $ by
      apply hlubd.mono
      apply fun n => (hLubEx n).lub_bound n
      exact fun _ ↦ hlubx

def ChainTrellis.lubYDiag
    {lubyc : C α}
    (hLubEx : ∀ n, Lub (ct.y n) (lubyc n))
    (hluby : Lub lubyc lubdx) (hlubd : Lub ct.diag lubd)
    : lubdx = lubd :=
  ida.le_antisymm _ _
    (by
      refine hluby.lub_least lubd fun n => (hLubEx n).lub_least lubd fun n1 => ?_
      -- get the value on the diagonal
      apply ida.le_trans _ (ct (n + n1) (n + n1)) _
      exact (hct.chain _ _ _ _ (Nat.le_add_left _ _) (Nat.le_add_right _ _))
      exact (hlubd.lub_bound (n + n1)))
    $ by
      apply hlubd.mono
      apply fun n => (hLubEx n).lub_bound n
      exact fun _ ↦ hluby

def ChainTrellis.lubCEq
    {lubxc : C α} {lubyc : C α}
    (hLubEx : ∀ n, Lub (ct.x n) (lubxc n))
    (hLubEy : ∀ n, Lub (ct.y n) (lubyc n))
    (hlubx : Lub lubxc lubx)
    (hluby : Lub lubyc luby)
    : lubx = luby :=
  le_antisymm
    (by
      refine hlubx.lub_least _ fun n => ?_
      refine (hLubEx n).lub_least _ fun n1 => ?_
      apply ida.le_trans _ _ _ _ (hluby.lub_bound n1)
      exact (hLubEy n1).lub_bound n)
    (by
      refine hluby.lub_least _ fun n => ?_
      refine (hLubEy n).lub_least _ fun n1 => ?_
      apply ida.le_trans _ _ _ _ (hlubx.lub_bound n1)
      exact (hLubEx n1).lub_bound n)

