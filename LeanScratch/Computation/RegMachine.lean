import LeanScratch.Vec
import LeanScratch.Fin2

namespace Comp

inductive RegTree
  | lf (n : Nat)
  | br (l r : RegTree)

abbrev RegTree.toStore : RegTree → Type
  | .lf n => Vec Nat n
  | .br l r => l.toStore × r.toStore

def Vec.zero {n} : Vec Nat n :=
  match n with
  | 0 => %[]
  | _+1 => 0 %::zero

def RegTree.toStore.zero {r : RegTree} : r.toStore :=
  match r with
  | .lf _ => Vec.zero
  | .br _ _ => ⟨zero, zero⟩

instance {r : RegTree} : Repr r.toStore where
  reprPrec v _ := f v
    where
      f {r : RegTree} (v : r.toStore) : Std.Format := match r with
      | .lf _ => repr v
      | .br _ _ => .bracket "⟨" (f v.fst ++ ", " ++ f v.snd) "⟩"

abbrev RegTree.toIdx : RegTree → Type
  | .lf n => Fin2 n
  | .br l r => l.toIdx ⊕ r.toIdx

-- Observation: any sequence of inc steps can be compressed into one large multi-reg inc
inductive RegMachine.Ins (r : RegTree) (L : Type)
  | inc (r : r.toIdx) (l : L)
  | dec (r : r.toIdx) (nzdest zdest : L)
  | hlt

def RegMachine (r : RegTree) (L : Type) := L → RegMachine.Ins r L

namespace RegMachine

structure Config (r : RegTree) (L : Type) :=
  regs : r.toStore
  state : L
deriving Repr

variable (machine : RegMachine r L)

def inc_vec {r} : Fin2 r → Vec Nat r → Vec Nat r
  | .fz, hd %:: tl => (hd + 1) %:: tl
  | .fs n, hd %:: tl => hd %:: inc_vec n tl

def inc : {r : RegTree} → r.toIdx → r.toStore → r.toStore
  | .lf _, idx, str => inc_vec idx str
  | .br _ _, .inl search, ⟨a, b⟩ => ⟨inc search a, b⟩
  | .br _ _, .inr search, ⟨a, b⟩ => ⟨a, inc search b⟩

def dec_vec {r} : Fin2 r → Vec Nat r → Option (Vec Nat r)
  | .fz, 0 %:: tl => .none
  | .fz, hd + 1 %:: tl => .some (hd %:: tl)
  | .fs n, hd %:: tl => dec_vec n tl |>.map (.cons hd)

def dec : {r : RegTree} → r.toIdx → r.toStore → Option r.toStore
  | .lf _, idx, str => dec_vec idx str
  | .br _ _, .inl search, ⟨a, b⟩ => (dec search a).map (⟨·, b⟩)
  | .br _ _, .inr search, ⟨a, b⟩ => (dec search b).map (⟨a, ·⟩)

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


def Config.step_n.add {start : Config r L} : start.step_n machine (a + b) = (start.step_n machine b).bind (·.step_n machine a) :=
  match b with
  | 0 => rfl
  | n+1 => by
    dsimp [step_n]
    by_cases h : ∃ w, (step machine start) = .some w
    · rcases h with ⟨w, p⟩
      simp only [p, Option.some_bind]
      exact step_n.add
    · simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h
      simp only [Option.none_bind, h]

def Config.trace (state : Config r L): Nat → List (Config r L)
  | 0 => []
  | n+1 => state :: match state.step machine with
    | .some next => next.trace n
    | .none => []

def StepsTo (start conn : Config r L) : Prop :=
  ∃ n, start.step_n machine n = .some conn

namespace StepsTo

theorem step
    (x : a.step machine = .some b)
    (h : StepsTo machine b c)
    : StepsTo machine a c := by
  rcases h with ⟨w, hb⟩
  refine ⟨w.succ, ?_⟩
  simp only [Config.step_n, x, Option.some_bind, hb]

def trans {m} : StepsTo m a b → StepsTo m b c → StepsTo m a c
  | ⟨w₁, p₁⟩, ⟨w₂, p₂⟩ =>
    ⟨w₂ + w₁, by simp only [Config.step_n.add, p₁, Option.some_bind, p₂] ⟩

instance {m : RegMachine r L} : Trans (StepsTo m) (StepsTo m) (StepsTo m) := ⟨trans⟩

def refl : StepsTo machien a a := ⟨0, rfl⟩

end StepsTo

/-- Terminates with -/
def TW (start term : Config r L) : Prop :=
  ∃ n, start.step_n machine n = .some term ∧ term.step machine = .none

namespace TW

def trans {m} : StepsTo m a b → TW m b c → TW m a c
  | ⟨w₁, p₁⟩, ⟨w₂, p₂, p₃⟩ =>
    ⟨w₂ + w₁, by simp [Config.step_n.add, p₁, p₂, p₃]⟩

instance {m : RegMachine r L} : Trans (StepsTo m) (TW m) (TW m) := ⟨trans⟩

theorem step
    (x : a.step machine = .some b)
    (h : TW machine b c)
    : TW machine a c := by
  rcases h with ⟨w, ha, hb⟩
  refine ⟨w.succ, ?_, hb⟩
  simp only [Config.step_n, x, Option.some_bind]
  exact ha

theorem refl (h : a.step machine = .none) : TW machine a a := ⟨0, rfl, h⟩

end TW

/- theorem TW_drive_lemma machine (correct : TW machine b c) : a.state = b.state → a.regs = b.regs → TW machine a c := -/
/-   fun seq regeq => match a, b with -/
/-     | ⟨ar, as⟩, ⟨br, bs⟩ => by simp_all only -/

end RegMachine

macro "drive" "TW" : tactic => `(tactic|
    repeat apply $(Lean.mkIdent ``RegMachine.TW.step) _ (by rfl); try {exact $(Lean.mkIdent ``RegMachine.TW.refl)      _ (by rfl)}
  )
macro "drive" "StepsTo" : tactic => `(tactic|
    repeat apply $(Lean.mkIdent ``RegMachine.StepsTo.step) _ (by rfl); try {apply $(Lean.mkIdent ``RegMachine.StepsTo.refl) }
  )
-- TODO
/- macro "drive" "with" term:term : tactic => `(tactic | { -/
/-   repeat apply RegMachine.TW_step _ (by rfl) -/
/-   apply RegMachine.TW_drive_lemma _ $term rfl -/
/- }) -/

class Computable (f : Vec Nat ina → Vec Nat outa) : Prop :=
  computable : ∃ L r, ∃ m : RegMachine (.br (.lf outa) $ .br (.lf ina) r) L,
    ∃ starts, ∀ inp : Vec Nat ina, ∃ e ends, m.TW
      ⟨⟨.zero, ⟨inp, .zero⟩⟩, starts⟩ ⟨⟨f inp, e⟩, ends⟩
