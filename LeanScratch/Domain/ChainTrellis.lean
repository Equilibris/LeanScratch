import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import LeanScratch.Domain.Lub

namespace Dom

variable [ida : PartialOrder α]

structure ChainTrellis (α : Type _) [PartialOrder α] where
  gen : Nat → Nat → α
  chain (n m n' m' : Nat) : n ≤ n' → m ≤ m' → gen n m ≤ gen n' m'

def ChainTrellis.x (v : ChainTrellis α) (x : Nat) : Chain α where
  gen := fun y => v.gen x y
  chain := fun y => v.chain _ _ _ _ (Nat.le_refl x) (Nat.le_succ y)
def ChainTrellis.y (v : ChainTrellis α) (y : Nat) : Chain α where
  gen := fun x => v.gen x y
  chain := fun x => v.chain _ _ _ _ (Nat.le_succ x) (Nat.le_refl y)

def ChainTrellis.xlubC (v : ChainTrellis α) (hLubEx : ∀ n, Lub (v.x n)) : Chain α where
  gen := fun n => (hLubEx n).lub
  chain := fun x => by
    apply Lub.mono
    intro y
    exact v.chain _ _ _ _ (Nat.le_succ x) (Nat.le_refl y)
def ChainTrellis.ylubC (v : ChainTrellis α) (hLubEy : ∀ n, Lub (v.y n)) : Chain α where
  gen := fun n => (hLubEy n).lub
  chain := fun y => by
    apply Lub.mono
    intro x
    exact v.chain _ _ _ _ (Nat.le_refl x) (Nat.le_succ y)

def ChainTrellis.diag (v : ChainTrellis α) : Chain α where
  gen := fun n => v.gen n n
  chain := fun n => v.chain _ _ _ _ (Nat.le_succ n) (Nat.le_succ n)

def ChainTrellis.lubXDiag
    {v : ChainTrellis α} (hLubEx : ∀ n, Lub (v.x n))
    (lubx : Lub (v.xlubC hLubEx)) (lubd : Lub v.diag)
    : lubx.lub = lubd.lub :=
  ida.le_antisymm _ _
    (by
      refine lubx.lub_least lubd.lub fun n => (hLubEx n).lub_least lubd.lub fun n1 => ?_
      -- get the value on the diagonal
      exact ida.le_trans _ (v.gen (n + n1) (n + n1)) _
        (v.chain _ _ _ _ (Nat.le_add_right _ _) (Nat.le_add_left _ _))
        (lubd.lub_bound (n + n1)))
    (lubd.mono fun n => (hLubEx n).lub_bound n)

def ChainTrellis.lubYDiag
    {v : ChainTrellis α} (hLubEy : ∀ n, Lub (v.y n))
    (lubx : Lub (v.ylubC hLubEy)) (lubd : Lub v.diag)
    : lubx.lub = lubd.lub :=
  ida.le_antisymm _ _
    (by
      refine lubx.lub_least lubd.lub fun n => (hLubEy n).lub_least lubd.lub fun n1 => ?_
      -- get the value on the diagonal
      exact ida.le_trans _ (v.gen (n + n1) (n + n1)) _
        (v.chain _ _ _ _ (Nat.le_add_left _ _) (Nat.le_add_right _ _))
        (lubd.lub_bound (n + n1)))
    (lubd.mono fun n => (hLubEy n).lub_bound n)

def ChainTrellis.lubCEq
    {v : ChainTrellis α} (hLubEx : ∀ n, Lub (v.x n)) (hLubEy : ∀ n, Lub (v.y n))
    (lubx : Lub (v.xlubC hLubEx)) (luby : Lub (v.ylubC hLubEy))
    : lubx.lub = luby.lub :=
  ida.le_antisymm _ _
    (by
      refine lubx.lub_least luby.lub fun n => ?_
      dsimp [ylubC]
      refine (hLubEx n).lub_least luby.lub fun n1 => ?_
      apply ida.le_trans _ _ _ _ (luby.lub_bound n1)
      dsimp [xlubC]
      exact (hLubEy n1).lub_bound n)
    (by
      refine luby.lub_least lubx.lub fun n => ?_
      dsimp [ylubC]
      refine (hLubEy n).lub_least lubx.lub fun n1 => ?_
      apply ida.le_trans _ _ _ _ (lubx.lub_bound n1)
      dsimp [xlubC]
      exact (hLubEx n1).lub_bound n)

