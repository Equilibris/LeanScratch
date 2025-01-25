import LeanScratch.Vec
import LeanScratch.Fin2

def Vec.zeros : (n : Nat) → Vec Nat n
  | 0 => %[]
  | _+1 => 0 %:: Vec.zeros _

namespace Comp

-- Observation: any sequence of inc steps can be compressed into one large multi-reg inc
inductive RegMachine.Ins (r : Nat) (L : Type)
  | inc (r : Fin2 r) (l : L)
  | dec (r : Fin2 r) (l1 l2 : L)
  | hlt

def RegMachine (r : Nat) (L : Type) := L → RegMachine.Ins r L

namespace RegMachine

structure Config (r : Nat) (L : Type) :=
  regs : Vec Nat r
  state : L
deriving Repr

variable (machine : RegMachine r L)

def inc {r} : Fin2 r → Vec Nat r → Vec Nat r
  | .fz, hd %:: tl => (hd + 1) %:: tl
  | .fs n, hd %:: tl => hd %:: inc n tl

def dec {r} : Fin2 r → Vec Nat r → Option (Vec Nat r)
  | .fz, 0 %:: tl => .none
  | .fz, hd + 1 %:: tl => .some (hd %:: tl)
  | .fs n, hd %:: tl => dec n tl |>.map (.cons hd)

def Config.step (state : Config r L) : Option $ Config r L :=
  let ⟨regs, state⟩ := state
  match machine state with
  | .inc r l => .some ⟨inc r regs, l⟩
  | .dec r l1 l2 =>
    match dec r regs with
    | .some regs => .some ⟨regs, l1⟩
    | .none      => .some ⟨regs, l2⟩
  | .hlt => .none

def Config.step_n (state : Config r L) : Nat → Option (Config r L)
  | 0 => state
  | n+1 => (state.step machine).bind (step_n · n)

def Config.trace (state : Config r L): Nat → List (Config r L)
  | 0 => []
  | n+1 => state :: match state.step machine with
    | .some next => next.trace n
    | .none => []

def TerminatesWith (start term : Config r L) : Prop :=
  ∃ n, start.step_n machine n = .some term ∧ term.step machine = .none

theorem TerminatesWith_step
    machine (x : a.step machine = .some b)
    (h : TerminatesWith machine b c)
    : TerminatesWith machine a c := by
  rcases h with ⟨w, ha, hb⟩
  refine ⟨w.succ, ?_, hb⟩
  simp only [Config.step_n, x, Option.some_bind]
  exact ha

theorem TerminatesWith_rfl machine (h : a.step machine = .none) : TerminatesWith machine a a := ⟨0, rfl, h⟩

end RegMachine

/- def Computable (f : Vec Nat ina → Vec Nat outa) : Prop := -/
/-   ∃ regc L s, ∃ m : RegMachine (outa + ina + regc) L, -/
/-     ∀ inp, ∃ (rst : Vec _ _), ∃ e, m.TerminatesWith ⟨padderA inp, s⟩ ⟨padderB (f inp), e⟩ -/
/-   where -/
/-     padderA {regc l} (ls : Vec Nat l) : Vec Nat (outa + l + regc) := -/
/-       match ls, regc with -/
/-       | _, 0   => sorry -/
/-       | z, n+1 => 0 %:: padderA z -/
/-     padderB {regc other l} (ls : Vec Nat l) :  Vec Nat (l + other + regc) := -/
/-       match ls, regc with -/
/-       | _, _ => sorry -/

