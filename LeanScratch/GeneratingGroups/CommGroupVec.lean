import LeanScratch.GeneratingGroups.Iso
import LeanScratch.GeneratingGroups.PowerRel
import Mathlib.Data.Vector.Defs

inductive GGMod.comm : rTy α
  | oo : GGMod.comm (.app (.obj a) (.obj b)) (.app (.obj b) (.obj a))
  | ii : GGMod.comm (.app (.inv a) (.inv b)) (.app (.inv b) (.inv a))
  | oi : GGMod.comm (.app (.obj a) (.inv b)) (.app (.inv b) (.obj a))

open Mathlib (Vector)

def pairToGrp {R : GGMod.rTy Bool} (vec : ℤ × ℤ) : GGMod (PowerRel R) :=
  let ⟨a, b⟩ := vec
  .app
    (if a > 0 then .obj ⟨False, a.natAbs⟩ else .inv (False, a.natAbs))
    (if a > 0 then .obj ⟨True,  b.natAbs⟩ else .inv (True,  b.natAbs))

def pairToGrp.inv.f : GGMod.GG (Bool × ℕ) → ℤ × ℤ
  | .unit => ⟨0, 0⟩
  | .obj (true, n)  => ⟨ n,  0⟩
  | .obj (false, n) => ⟨ 0,  n⟩
  | .inv (true, n)  => ⟨-n,  0⟩
  | .inv (false, n) => ⟨ 0, -n⟩
  | .app a b =>
    let ⟨a₁, b₁⟩ := f a
    let ⟨a₂, b₂⟩ := f b
    ⟨a₁ + a₂, b₁ + b₂⟩
def pairToGrp.inv {R : GGMod.rTy Bool} (x : GGMod (PowerRel R)) : ℤ × ℤ :=
  x.lift pairToGrp.inv.f (by
    introv h
    induction h
    <;> try simp only [pairToGrp.inv.f, Int.add_zero, Prod.mk.eta, Prod.mk.injEq, Int.zero_add, Prod.mk.eta]

    case objInv a =>
      rcases a with ⟨a, b⟩
      cases b
      <;> cases a
      <;> simp only [pairToGrp.inv.f, Int.natCast_add, Int.Nat.cast_ofNat_Int, Int.add_zero, true_and, Int.neg_zero, Int.add_zero, and_self, and_true]
      <;> rw [←Int.zero_add (_ + _), ←Int.add_assoc, Int.add_neg_cancel_right]
    case invObj a =>
      rcases a with ⟨a, b⟩
      cases b
      <;> cases a
      <;> simp only [pairToGrp.inv.f, Int.natCast_add, Int.Nat.cast_ofNat_Int, Int.add_zero, true_and, Int.neg_zero, Int.add_zero, and_self, and_true]
      <;> rw [←Int.zero_add (_ + _), ←Int.add_assoc, Int.neg_add_cancel_right]
    case assoc a b c => simp only [Int.add_assoc, and_self]
    case trans a b => exact a.trans b
    case symm a => exact a.symm
    case base a => sorry
    case homo a b => simp only [a, b, and_self]
    )

open Function in
def pairToGrp.bij { R } : Bijective (@pairToGrp R) := by
  apply bijective_iff_has_inverse.mpr
  use pairToGrp.inv
  constructor
  · simp only [LeftInverse]
    introv
    rcases x with ⟨a, b⟩
    cases a
    <;> cases b
    <;> simp [pairToGrp, inv]
    · sorry
    · sorry
    · sorry
    · sorry

  · sorry

/- def vToGrp {R : GGMod.rTy (Fin n)} (vec : Vector ℤ n) : GGMod (PowerRel R) := -/
/-   let ⟨w, p⟩ := vec -/
/-   w.foldlIdx (fun i last next => -/
/-     have : i < n := sorry -/
/-     if next > 0 then .app (.obj ⟨⟨i, this⟩, next.natAbs⟩) .unit -/
/-     else .app last (.inv ⟨⟨i, this⟩, next.natAbs⟩)) .unit -/

/- def grpToV {R : GGMod.rTy (Fin n)} (vec : Vector ℤ n) : GGMod (PowerRel R) := -/
/-   let ⟨w, p⟩ := vec -/
/-   w.foldlIdx (fun i last next => -/
/-     have : i < n := sorry -/
/-     if next > 0 then .app (.obj ⟨⟨i, this⟩, next.natAbs⟩) .unit -/
/-     else .app last (.inv ⟨⟨i, this⟩, next.natAbs⟩)) .unit -/
