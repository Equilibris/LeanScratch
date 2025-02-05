import LeanScratch.Computation.RegMachine

namespace Comp

def addf : Vec Nat 2 → Vec Nat 1 := fun | %[a, b] => %[a + b]

namespace addf
def prog : RegMachine (.br (.lf 1) (.br (.lf 2) (.lf 0))) (Fin 5) := fun
  | 0 => .dec (.inr $ .inl $ .fz) 1 2
  | 1 => .inc (.inl .fz) 0

  | 2 => .dec (.inr $ .inl $ .fs .fz) 3 4
  | 3 => .inc (.inl .fz) 2

  | 4 => .hlt

abbrev prog.ex : RegMachine.Config (.br (.lf 1) (.br (.lf 2) (.lf 0))) (Fin 5) := {regs := ⟨%[0], ⟨%[1,2], %[]⟩⟩, state := 0}

/--
info: [{ regs := ⟨%[0], ⟨%[1, 2], %[]⟩⟩, state := 0 },
 { regs := ⟨%[0], ⟨%[0, 2], %[]⟩⟩, state := 1 },
 { regs := ⟨%[1], ⟨%[0, 2], %[]⟩⟩, state := 0 },
 { regs := ⟨%[1], ⟨%[0, 2], %[]⟩⟩, state := 2 },
 { regs := ⟨%[1], ⟨%[0, 1], %[]⟩⟩, state := 3 },
 { regs := ⟨%[2], ⟨%[0, 1], %[]⟩⟩, state := 2 },
 { regs := ⟨%[2], ⟨%[0, 0], %[]⟩⟩, state := 3 },
 { regs := ⟨%[3], ⟨%[0, 0], %[]⟩⟩, state := 2 },
 { regs := ⟨%[3], ⟨%[0, 0], %[]⟩⟩, state := 4 }]
-/
#guard_msgs in #eval RegMachine.Config.trace prog prog.ex 10

theorem prog.term : prog.TW ⟨⟨%[n], ⟨%[x, y], %[]⟩⟩, 0⟩ ⟨⟨%[n + x + y], .zero⟩, 4⟩ := by
  induction x generalizing n
  case succ x ih =>
    drive TW
    rw [Nat.add_comm x, ←Nat.add_assoc]
    exact ih
  drive TW
  induction y generalizing n
  case succ x ih =>
    drive TW
    rw [Nat.add_comm x, ←Nat.add_assoc]
    exact ih
  drive TW

instance computable : Computable addf :=
  ⟨_, _, prog, 0,
    fun | %[x, y] => ⟨.zero, 4, by
      simp only [addf]
      rw [←Nat.zero_add (x + y), ←Nat.add_assoc]
      exact prog.term⟩⟩

end addf

def projf : Vec Nat 2 → Vec Nat 1 := fun | %[a, _] => %[a]
/- def projf (x : Fin2 n) : Vec Nat n → Vec Nat 1 := fun arr => %[arr.lookup x] -/

namespace projf

def prog : RegMachine (.br (.lf 1) (.br (.lf 2) (.lf 0))) (Fin 3) := fun
  | 0 => .dec (.inr $ .inl .fz) 1 2
  | 1 => .inc (.inl .fz) 0
  | 2 => .hlt

theorem prog.term : prog.TW ⟨⟨%[n], ⟨%[x, y], %[]⟩⟩, 0⟩ ⟨⟨%[n + x], ⟨%[0, y], %[]⟩⟩, 2⟩ := by
  induction x generalizing n
  case succ x ih =>
    drive TW
    rw [Nat.add_comm x, ←Nat.add_assoc]
    exact ih
  drive TW


instance computable : Computable projf :=
  ⟨_, _, prog, 0,
    fun | %[x, y] => ⟨⟨%[0, y], %[]⟩, 2, by
      simp only [projf]
      nth_rw 2 [←Nat.zero_add x]
      exact prog.term⟩⟩

end projf

def constf (n : Nat) : Vec Nat 1 → Vec Nat 1 := fun _ => %[n]

namespace constf

def prog (n : Nat) : RegMachine (.br (.lf 1) (.br (.lf 1) (.lf 0))) (Fin n.succ) := fun
  | 0 => .hlt
  | ⟨n+1, p⟩ => .inc (.inl .fz) ⟨n, by omega⟩

theorem prog.term : (prog n₁).TW ⟨⟨%[n₂], ⟨%[y], %[]⟩⟩, ⟨k, p⟩⟩ ⟨⟨%[n₂ + k], ⟨%[y], %[]⟩⟩, 0⟩ := by
  induction k generalizing n₂
  case succ x ih =>
    drive TW
    nth_rw 1 [Nat.add_comm x]
    rw [←Nat.add_assoc]
    exact ih
  exact RegMachine.TW.refl _ (by rfl)

instance computable n : Computable (constf n) :=
  ⟨_, _, prog n, ⟨n, by omega⟩,
    fun | %[z] => ⟨⟨%[z], %[]⟩, ⟨0, Nat.zero_lt_succ _⟩, by
      simp only [constf]
      -- nth_rw breaks
      have : (n %:: %[]) = ((0 + n) %:: %[]) := by rw [Nat.zero_add]
      rw [this]
      exact prog.term⟩⟩

end constf

def subf : Vec Nat 2 → Vec Nat 1 := fun | %[a, b] => %[a - b]

namespace subf

def prog : RegMachine (.br (.lf 1) (.br (.lf 2) (.lf 0))) (Fin 5) :=
  let a := .inr $ .inl $ .fs .fz
  let b := .inr $ .inl $ .fz
  let o := .inl .fz
  fun
  | 0 => .dec a 1 2
  | 1 => .dec b 0 0
  | 2 => .dec b 3 4
  | 3 => .inc o 2
  | 4 => .hlt

theorem prog.term : prog.TW ⟨⟨%[n], ⟨%[x, y], %[]⟩⟩, 0⟩ ⟨⟨%[n + (x - y)], ⟨%[0, 0], %[]⟩⟩, 4⟩ := by
  induction y generalizing x n
  case succ x' ih =>
    cases x
    <;> drive TW
    case zero =>
      have : (0 - (x' + 1)) = (0 - x') := by omega
      rw [this]
      exact ih
    case succ n'=>
      rw [Nat.add_sub_add_right n' 1 x']
      exact ih
  change prog.TW _ ⟨⟨%[n + x], _⟩, _⟩
  drive TW
  induction x generalizing n
  case succ x ih =>
    drive TW
    rw [Nat.add_comm x, ←Nat.add_assoc]
    exact ih
  case zero =>
  drive TW

instance computable : Computable subf :=
  ⟨_, _, prog, 0, fun %[x, y] => ⟨.zero, 4, by
    simp only [Fin.isValue, subf]
    rw [←Nat.zero_add (x - y)]
    exact prog.term⟩⟩

end subf

def divmodf : Vec Nat 2 → Vec Nat 2 := fun | %[a, b] => %[a / b, a % b]

namespace divmodf

inductive DivSteps
  | check : Fin 4 → DivSteps
  | copy  : Fin 5 → DivSteps
  | sub   : Fin 3 → DivSteps
  | exit  : Fin 5 → DivSteps
  | hlt   : DivSteps

/- out | num | denom | scratch -/
def prog : RegMachine (.br (.lf 2) (.br (.lf 2) (.lf 2))) DivSteps :=
  let out   := .inl        $     .fz
  let rem   := .inl        $ .fs .fz
  let num   := .inr $ .inl $     .fz
  let denom := .inr $ .inl $ .fs .fz
  let sca   := .inr $ .inr $     .fz
  let scb   := .inr $ .inr $ .fs .fz
  fun
  | .check 0 => .dec denom (.check 1) (.check 2)
  | .check 1 => .inc denom (.copy  0)
  | .check 2 => .dec num   (.check 3) (.hlt)
  | .check 3 => .inc rem   (.check 2)

  | .copy  0 => .dec denom (.copy  1) (.copy 3)
  | .copy  1 => .inc sca   (.copy  2)
  | .copy  2 => .inc scb   (.copy  0)
  | .copy  3 => .dec scb   (.copy  4) (.sub  0)
  | .copy  4 => .inc denom (.copy  3)

  | .sub   0 => .dec sca   (.sub   1) (.sub  2)
  | .sub   1 => .dec num   (.sub   0) (.exit 0)
  | .sub   2 => .inc out   (.copy  0)

  | .exit  0 => .inc sca   (.exit  1) -- Fix error with dec in sub 0

  | .exit  1 => .dec sca   (.exit  2) (.exit 3) -- The R branch will never be taken
  | .exit  2 => .dec denom (.exit  1) (.exit 3)
  | .exit  3 => .dec denom (.exit  4) (.hlt)
  | .exit  4 => .inc rem   (.exit  3)

  | .hlt    => .hlt

theorem prog.copy_step : prog.StepsTo
    ⟨⟨%[out, o2], ⟨%[num, denom], %[n,         n]⟩⟩,         .copy 0⟩
    ⟨⟨%[out, o2], ⟨%[num, 0],     %[n + denom, n + denom]⟩⟩, .copy 3⟩ := by
  induction denom generalizing n
  · apply RegMachine.StepsTo.step _ (by rfl)
    apply RegMachine.StepsTo.refl
  case succ ih =>
    drive StepsTo
    dsimp [RegMachine.inc, RegMachine.inc_vec]
    repeat nth_rw 3 [Nat.add_comm _ 1]
    rw [←Nat.add_assoc]
    exact ih

theorem prog.copy_finish : prog.StepsTo
    ⟨⟨%[out, o2], ⟨%[num, denom],     %[n, m]⟩⟩, .copy 3⟩
    ⟨⟨%[out, o2], ⟨%[num, denom + m], %[n, 0]⟩⟩, .sub 0⟩ := by
  induction m generalizing denom
  · drive StepsTo
  case succ ih =>
    drive StepsTo
    dsimp [RegMachine.inc, RegMachine.inc_vec]
    nth_rw 2 [Nat.add_comm _ 1]
    rw [←Nat.add_assoc]
    exact ih

theorem prog.sub_step (hlt : n ≤ num) : prog.StepsTo
    ⟨⟨%[out    , o2], ⟨%[num,     denom], %[n, m]⟩⟩, .sub 0⟩
    ⟨⟨%[out + 1, o2], ⟨%[num - n, denom], %[0, m]⟩⟩, .copy 0⟩ := by
  induction n generalizing num
  · drive StepsTo
  case succ n ih =>
    drive StepsTo
    cases num; · contradiction
    drive StepsTo
    simp only [Fin.isValue, Nat.reduceSubDiff]
    exact ih (Nat.le_of_lt_succ hlt)

theorem prog.sup_step (hlt : num < n) : prog.StepsTo
    ⟨⟨%[out, o2], ⟨%[num, denom], %[n,       m]⟩⟩, .sub 0⟩
    ⟨⟨%[out, o2], ⟨%[0,   denom], %[n - num, m]⟩⟩, .exit 1⟩ := by
  induction num generalizing n
  <;> cases n
  <;> (try exact (Nat.not_succ_le_zero _ hlt).elim)
  <;> (try simp only [Fin.isValue,
        Nat.add_lt_add_iff_right,
        Nat.reduceSubDiff] at hlt ⊢)
  <;> drive StepsTo
  case succ.succ _ ih _ => exact ih hlt

theorem prog.exit_cycle_d (hlt : n ≤ denom) : prog.StepsTo
    ⟨⟨%[out, o2], ⟨%[num, denom],     %[n, m]⟩⟩, .exit 1⟩
    ⟨⟨%[out, o2], ⟨%[num, denom - n], %[0, m]⟩⟩, .exit 3⟩ := by
  induction n generalizing denom
  <;> drive StepsTo
  case succ n ih =>
    cases denom
    · exact (Nat.not_succ_le_zero n hlt).elim
    next denom =>
      rw [Nat.add_sub_add_right ]
      drive StepsTo
      exact ih (by exact Nat.le_of_lt_succ hlt)

theorem prog.exit_cycle_r : prog.TW
    { regs := (%[out, out2],       %[0, num], %[0, 0]), state := DivSteps.exit 3 }
    { regs := (%[out, out2 + num], %[0, 0  ], %[0, 0]), state := DivSteps.hlt } := by
  induction num generalizing out2
  <;> drive TW
  case succ ih =>
    rw [Nat.add_comm _ 1, ←Nat.add_assoc]
    exact ih

theorem prog.nz {denom : Nat} : prog.TW
    ⟨⟨%[out                   , out2                   ], ⟨%[num, denom.succ], %[0, 0]⟩⟩, .copy 0⟩
    ⟨⟨%[out + num / denom.succ, out2 + num % denom.succ], ⟨%[0,   0         ], %[0, 0]⟩⟩, .hlt⟩ := by
  apply RegMachine.TW.trans prog.copy_step
  apply RegMachine.TW.trans prog.copy_finish
  simp only [zero_add, Fin.isValue]
  by_cases hlt : denom.succ ≤ num
  · apply RegMachine.TW.trans (prog.sub_step hlt) _
    rw [Nat.div_eq_sub_div (Nat.zero_lt_succ _) hlt, Nat.mod_eq_sub_mod hlt]
    nth_rw 2 [Nat.add_comm _ 1]
    rw [←Nat.add_assoc]
    exact prog.nz
  · have hlt' : num < denom.succ := Nat.gt_of_not_le hlt
    clear hlt
    rw [(Nat.div_eq_zero_iff $ Nat.zero_lt_succ denom).mpr hlt',
        (Nat.mod_eq_of_lt hlt'),
        Nat.add_zero]
    apply RegMachine.TW.trans (prog.sup_step hlt')
    apply RegMachine.TW.trans (prog.exit_cycle_d (Nat.sub_le denom.succ num))
    have : denom.succ - (denom.succ - num) = num := by omega
    rw [this]
    exact prog.exit_cycle_r

theorem prog.z : prog.TW
    ⟨⟨%[0, out2      ], ⟨%[num, 0], %[0, 0]⟩⟩, .check 2⟩
    ⟨⟨%[0, out2 + num], ⟨%[0,   0], %[0, 0]⟩⟩, .hlt⟩ := by
  induction num generalizing out2
  · drive TW
  case succ ih =>
    nth_rw 2 [Nat.add_comm _ 1]
    rw [←Nat.add_assoc]
    drive TW
    exact ih

theorem prog.term : prog.TW
    ⟨⟨%[0          , 0],           ⟨%[num, denom], %[0, 0]⟩⟩, .check 0⟩
    ⟨⟨%[num / denom, num % denom], ⟨%[0,   0    ], %[0, 0]⟩⟩, .hlt⟩ :=
  match denom with
  | 0 => by
    drive TW
    rw [Nat.div_zero, Nat.mod_zero]
    nth_rw 2 [←Nat.zero_add num]
    exact prog.z
  | denom+1 => by
    apply RegMachine.TW.step _ (by rfl)
    apply RegMachine.TW.step _ (by rfl)
    rw [←Nat.zero_add (num / (denom + 1)), ←Nat.zero_add (num % (denom + 1))]
    exact prog.nz

instance computable : Computable divmodf :=
  ⟨_, _, prog, .check 0, fun %[_, _] => ⟨.zero, .hlt, prog.term⟩⟩

end divmodf

def exp2 : Vec Nat 1 → Vec Nat 1 := fun %[x] => %[Nat.pow 2 x]

namespace exp2

inductive ExpSteps
  | init
  | cond
  | mvo : Fin 2 → ExpSteps
  | dbl : Fin 3 → ExpSteps
  | hlt

def prog : RegMachine (.br (.lf 1) (.br (.lf 1) (.lf 1))) ExpSteps :=
  let out   := .inl        $ .fz
  let inp   := .inr $ .inl $ .fz
  let store := .inr $ .inr $ .fz
  fun
  | .init  => .inc out   (.dbl 0)
  | .cond  => .dec inp   (.mvo 0) (.hlt)
  | .mvo 0 => .dec out   (.mvo 1) (.dbl 0)
  | .mvo 1 => .inc store (.mvo 0)
  | .dbl 0 => .dec store (.dbl 1) (.cond)
  | .dbl 1 => .inc out   (.dbl 2)
  | .dbl 2 => .inc out   (.dbl 0)
  | .hlt   => .hlt

def prog.mvo : prog.StepsTo
    ⟨⟨%[out], ⟨%[inp], %[s      ]⟩⟩, .mvo 0⟩
    ⟨⟨%[0],   ⟨%[inp], %[s + out]⟩⟩, .dbl 0⟩ := by
  induction out generalizing s
  · drive StepsTo
  case succ ih =>
    nth_rw 2 [←Nat.add_comm 1]
    rw [←Nat.add_assoc]
    drive StepsTo
    exact ih

def prog.dbl : prog.StepsTo
    ⟨⟨%[out],         ⟨%[inp], %[s]⟩⟩, .dbl 0⟩
    ⟨⟨%[out + s + s], ⟨%[inp], %[0]⟩⟩, .cond⟩ := by
  induction s generalizing out
  · simp only [Fin.isValue, add_zero, zero_add]
    drive StepsTo
  case succ n ih =>
    drive StepsTo
    rw [Nat.add_comm _ 1]
    have : out + (1 + n) + (1 + n) = out + 2 + n + n := by omega
    rw [this]
    exact ih

def prog.double : prog.StepsTo
    ⟨⟨%[out],       ⟨%[inp], %[0]⟩⟩, .mvo 0⟩
    ⟨⟨%[out * 2],   ⟨%[inp], %[0]⟩⟩, .cond⟩ := by
  apply RegMachine.StepsTo.trans prog.mvo
  rw [Nat.zero_add]
  apply RegMachine.StepsTo.trans prog.dbl
  rw [Nat.zero_add, Nat.mul_two _]
  apply RegMachine.StepsTo.refl

def prog.body : prog.TW
    ⟨⟨%[out],                 ⟨%[inp], %[0]⟩⟩, .cond⟩
    ⟨⟨%[out * Nat.pow 2 inp], ⟨%[0],   %[0]⟩⟩, .hlt⟩ := by
  induction inp generalizing out
  · simp only [Nat.pow_eq, pow_zero, mul_one]
    drive TW
  case succ ih =>
    drive TW
    dsimp
    apply RegMachine.TW.trans prog.double
    rw [Nat.pow_succ]
    nth_rw 3 [Nat.mul_comm]
    rw [←Nat.mul_assoc]
    exact ih

def prog.term : prog.TW
    ⟨⟨%[0],             ⟨%[inp], %[0]⟩⟩, .init⟩
    ⟨⟨%[Nat.pow 2 inp], ⟨%[0],   %[0]⟩⟩, .hlt⟩ := by
  drive TW
  dsimp [RegMachine.inc, RegMachine.inc_vec]
  rw [←Nat.one_mul (2 ^ inp)]
  exact prog.body

instance computable : Computable exp2 :=
  ⟨_, _, prog, .init, fun %[_] => ⟨.zero, .hlt, prog.term⟩⟩

end exp2

-- Cool idea that i can try: rather than making programs their own atomic
-- concepts i can add functions doing certian operations on sub-structures
-- of programs and then transforming these in a certian way alowing for
-- sub-programs to be encoded and so on.


