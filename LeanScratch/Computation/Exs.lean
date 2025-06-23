import LeanScratch.Computation.RegMachine
import LeanScratch.Computation.RegMachine.Subroutine
import LeanScratch.Computation.ComputableFuns
import LeanScratch.Computation.ComputableFuns.RegMachine

namespace Comp

section Q1

/- def copyProg : RegMachine (.br (.lf 1) (.br (.lf 1) (.lf 1))) (Fin 6) := fun -/
/-   | 0 => .dec (.inr $ .inl $ .fz) 1 2 -/
/-   | 1 => .inc (.inr $ .inr $ .fz) 0 -/
/-   | 2 => .dec (.inr $ .inr $ .fz) 3 5 -/
/-   | 3 => .inc (.inr $ .inl $ .fz) 4 -/
/-   | 4 => .inc (.inl $ .fz) 2 -/
/-   | 5 => .hlt -/

/- theorem copyProg.term : copyProg.TW ⟨⟨%[n], ⟨%[m], %[k]⟩⟩, 0⟩ ⟨⟨%[n + m + k], ⟨%[m], %[k]⟩⟩, 5⟩ -/

-- Cool idea that i can try: rather than making programs their own atomic
-- concepts i can add functions doing certian operations on sub-structures
-- of programs and then transforming these in a certian way alowing for
-- sub-programs to be encoded and so on.

-- I started work on this rather than the logarithm task as ive done so many already

end Q1

namespace Q2

/-
  We simply build programs with dead-code in the following way:
  - Take n decrement steps on the output register,
  - Continue with original program.
-/

-- Parameter for program generation
variable (n : Nat)

-- Instance to inherit from
variable {f : Pfn 1 1} [compInst : Pfn.Computable f] [decEq : DecidableEq compInst.L]

inductive ProgSteps
  | src : compInst.L → ProgSteps
  | new : Fin n.succ → ProgSteps

instance {n} : DecidableEq (ProgSteps n (compInst := compInst)) := fun
  | .src a, .src b =>
    match decEq a b with
    | .isTrue p => p.rec $ .isTrue rfl
    | .isFalse p => .isFalse (p ∘ (ProgSteps.src.injEq _ _).mp)
  | .new a, .new b => 
    if h : a = b then h.rec $ .isTrue rfl
    else .isFalse (h ∘ (ProgSteps.new.injEq _ _).mp)
  | .src a, .new b | .new a, .src b => .isFalse ProgSteps.noConfusion

instance : Fintype2 (ProgSteps n (compInst := compInst)) where
  elems :=
    Fintype2.elems.map ProgSteps.src ++
    Fintype2.elems.map ProgSteps.new
  complete := fun x => by cases x <;> simp [Fintype2.complete]
  nodup := by
    simp only [Nat.succ_eq_add_one, List.nodup_append, List.Disjoint, List.mem_map, imp_false,
      not_exists, not_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      not_false_eq_true, implies_true, and_true]
    refine ⟨?_, ?_⟩
    <;> apply List.Nodup.map
    <;> try (exact Fintype2.nodup)
    · exact @ProgSteps.src.inj _ _ _
    · exact @ProgSteps.new.inj _ _ _

def prog : RegMachine (.br (.lf 1) (.br (.lf 1) compInst.r)) (ProgSteps n (compInst := compInst))
  | .src v => match compInst.m v with
    | .hlt => .hlt
    | .inc r next => .inc r (.src next)
    | .dec r l1 l2 => .dec r (.src l1) (.src l2)
  | .new 0 =>
    .dec
      (.inl $ .fz)
      (.src compInst.startins)
      (.src compInst.startins)
  | .new ⟨n+1, p⟩ =>
    .dec
      (.inl $ .fz)
      (.new ⟨n, Nat.lt_of_succ_lt p⟩)
      (.new ⟨n, Nat.lt_of_succ_lt p⟩)

-- This is quite straight forward but sadly i didnt have time to do it
example : Pfn.Computable f := sorry

end Q2

namespace Q3

inductive ProgSteps
  | exit
  | halt
  | setup : Fin 2 → ProgSteps
  | mov   : Fin 2 → ProgSteps
  | half  : Fin 3 → ProgSteps
  | inca
deriving DecidableEq, Repr

instance : Fintype2 ProgSteps where
  elems :=
    Fintype2.elems.map .mov ++
    Fintype2.elems.map .half ++
    Fintype2.elems.map .setup ++
    [ .exit, .inca, .halt ]
  complete := fun x => by cases x <;> simp [Fintype2.complete]
  nodup := by
    simp only [List.append_assoc, List.nodup_append, List.nodup_cons, List.mem_cons,
      List.mem_singleton, or_self, not_false_eq_true, List.not_mem_nil, List.nodup_nil, and_self,
      List.Disjoint, List.mem_map, imp_false, not_or, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, implies_true, and_true, List.mem_append, not_exists, not_and]
    refine ⟨?_, ?_, ?_⟩
    <;> apply List.Nodup.map
    <;> try (exact Fintype2.nodup)
    exact @ProgSteps.mov.inj
    exact @ProgSteps.half.inj
    exact @ProgSteps.setup.inj


def prog : RegMachine (.lf 3) ProgSteps :=
  let a := .fz
  let s := .fs $ .fz
  let z := .fs $ .fs $ .fz
  fun
  | .exit | .halt => .hlt
  | .setup 0 => .dec a (.setup 0) (.setup 1)
  | .setup 1 => .dec s (.mov   0) (.exit)
  | .mov   0 => .inc z (.mov   1)
  | .mov   1 => .dec s (.mov   0) (.half  0)
  | .half  0 => .dec z (.half  1) (.inca)
  | .half  1 => .dec z (.half  2) (.halt)
  | .half  2 => .inc s (.half  0)
  | .inca    => .inc a (.mov   1)

def prog.mov : prog.StepsTo
    ⟨%[a, s, z], .mov 0⟩
    ⟨%[a, 0, z + s + 1], .half 0⟩ := by
  induction s generalizing z
  · drive StepsTo
  case succ s ih =>
    nth_rw 3 [Nat.add_comm _ 1]
    rw [←Nat.add_assoc]
    apply RegMachine.StepsTo.step _ (by rfl)
    apply RegMachine.StepsTo.step _ (by rfl)
    exact ih

def prog.mov' : prog.StepsTo
    ⟨%[a, s, z], .mov 1⟩
    ⟨%[a, 0, z + s], .half 0⟩ := by
  induction s generalizing z
  · drive StepsTo
  case succ s ih =>
    nth_rw 2 [Nat.add_comm _ 1]
    rw [←Nat.add_assoc]
    drive StepsTo
    exact ih

def prog.loop_even : prog.StepsTo
    ⟨%[a, s    , z + z], .half 0⟩
    ⟨%[a, s + z, 0    ], .inca⟩ := by
  induction z generalizing s
  · drive StepsTo
  case succ z ih =>
    rw [Nat.add_assoc, Nat.add_comm _ (z + 1), ←Nat.add_assoc, ←Nat.add_assoc]
    drive StepsTo
    dsimp [RegMachine.inc, RegMachine.inc_vec]
    nth_rw 2 [Nat.add_comm _ 1]
    rw [←Nat.add_assoc]
    exact ih
def prog.loop_odd : prog.TW
    ⟨%[a, s    , z + z + 1], .half 0⟩
    ⟨%[a, s + z, 0        ], .halt⟩ := by
  induction z generalizing s
  · drive TW
  case succ z ih =>
    rw [←Nat.add_assoc, Nat.add_comm (z + 1), ←Nat.add_assoc]-- Nat.add_comm _ (z + 1), ←Nat.add_assoc, ←Nat.add_assoc]
    apply RegMachine.TW.step _ (by rfl)
    apply RegMachine.TW.step _ (by rfl)
    apply RegMachine.TW.step _ (by rfl)
    dsimp [RegMachine.inc, RegMachine.inc_vec]
    nth_rw 3 [Nat.add_comm _ 1]
    rw [←Nat.add_assoc]
    exact ih

def prog.full_loop_even : prog.StepsTo
    ⟨%[a    , s, z + z], .half 0⟩
    ⟨%[a + 1, 0, s + z], .half 0⟩ := by
  apply RegMachine.StepsTo.trans prog.loop_even
  drive StepsTo
  nth_rw 2 [←Nat.zero_add (s + z)]
  exact prog.mov'

def prog.nz : prog.TW
    ⟨%[out, 0, (y * 2 + 1) * 2 ^ a], .half 0⟩
    ⟨%[out + a, y, 0], .halt⟩ := by
  induction a generalizing out
  · rw [pow_zero, mul_one, add_zero, Nat.mul_two]
    nth_rw 3 [←Nat.zero_add y]
    exact prog.loop_odd
  case succ a ih =>
    rw [Nat.pow_succ, ←Nat.mul_assoc, Nat.mul_two]
    apply RegMachine.TW.trans prog.full_loop_even
    rw [Nat.zero_add, Nat.add_comm a 1, ←Nat.add_assoc]
    exact ih

/-
  The program is the inverse of the pair-coding functions we were given
  in lectures. This stores the two numbers in a and s respectrively.
-/

end Q3

