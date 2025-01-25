import LeanScratch.Computation.RegMachine

namespace Comp

namespace Ex1
def ex_prog : RegMachine 3 (Fin 5) := fun
  | ⟨0, _⟩ => .dec (.fs .fz) 1 2
  | ⟨1, _⟩ => .inc .fz 0
  | ⟨2, _⟩ => .dec (.fs $ .fs .fz) 3 4
  | ⟨3, _⟩ => .inc .fz 2
  | ⟨4, _⟩ => .hlt

abbrev ex_prog.init : RegMachine.Config 3 (Fin 5) := {regs := %[0, 1, 2], state := 0}

/--
info: [{ regs := %[0, 1, 2], state := 0 },
 { regs := %[0, 0, 2], state := 1 },
 { regs := %[1, 0, 2], state := 0 },
 { regs := %[1, 0, 2], state := 2 },
 { regs := %[1, 0, 1], state := 3 },
 { regs := %[2, 0, 1], state := 2 },
 { regs := %[2, 0, 0], state := 3 },
 { regs := %[3, 0, 0], state := 2 },
 { regs := %[3, 0, 0], state := 4 }]
-/
#guard_msgs in #eval RegMachine.Config.trace ex_prog ex_prog.init 32

example : ex_prog.TerminatesWith ⟨%[n, x, y], 0⟩ ⟨%[n + x + y, 0, 0], 4⟩ := by
  induction x generalizing n
  case succ x ih =>
    apply ex_prog.TerminatesWith_step (by rfl)
    apply ex_prog.TerminatesWith_step (by rfl)
    dsimp [RegMachine.inc]
    rw [Nat.add_comm x, ←Nat.add_assoc]
    exact ih
  apply ex_prog.TerminatesWith_step (by rfl)

  induction y generalizing n
  case succ x ih =>
    apply ex_prog.TerminatesWith_step (by rfl)
    apply ex_prog.TerminatesWith_step (by rfl)
    dsimp [RegMachine.inc]
    rw [Nat.add_comm x, ←Nat.add_assoc]
    exact ih
  apply ex_prog.TerminatesWith_step (by rfl)
  apply ex_prog.TerminatesWith_rfl
  rfl

end Ex1

