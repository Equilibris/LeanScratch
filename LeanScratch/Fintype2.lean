import Mathlib.Init.Data.List.Basic
import Mathlib.Data.List.Nodup

class Fintype2 (α : Type u) where
  /-- The `Finset` containing all elements of a `Fintype` -/
  elems : List α
  /-- A proof that `elems` contains every element of the type -/
  complete : ∀ x : α, x ∈ elems
  nodup : elems.Nodup

instance Fin.instFintype2 : Fintype2 (Fin n) := match n with
  | 0 => ⟨[], fun ⟨_, p⟩ => (Nat.not_succ_le_zero _ p).elim, .nil⟩
  | n + 1 =>
    let ⟨elems, complete, pw⟩:= instFintype2 (n := n)
    ⟨⟨0, Nat.zero_lt_succ _⟩ :: .map .succ elems, fun
      | ⟨0, p⟩ => List.mem_cons_self _ _
      | ⟨n'+1, p⟩ => by
        simp only [zero_eta, List.mem_cons, List.mem_map, complete, true_and]
        exact .inr ⟨⟨n', Nat.succ_lt_succ_iff.mp p⟩, rfl⟩,
      .cons
        (by simp only [zero_eta, List.mem_map, not_exists, not_and]; exact fun x _ => succ_ne_zero x) 
        ((List.Nodup.map (fun ⟨x, p₁⟩ ⟨y, p₂⟩ h => by injections; simp_all) pw))⟩

