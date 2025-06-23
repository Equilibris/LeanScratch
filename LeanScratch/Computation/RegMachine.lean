import LeanScratch.Computation.RegMachine.RegTree

namespace Comp

inductive RegMachine.Ins (r : RegTree) (L : Type)
  | inc (r : r.toIdx) (l : L)
  | dec (r : r.toIdx) (nzdest zdest : L)
  | hlt

def RegMachine (r : RegTree) (L : Type) [Fintype2 L] := L → RegMachine.Ins r L

namespace RegMachine

structure Config (r : RegTree) (L : Type) :=
  regs : r.toStore
  state : L
deriving Repr

variable [Fintype2 L] (machine : RegMachine r L)

def inc_vec {r} : Fin2 r → Vec Nat r → Vec Nat r
  | .fz, hd %:: tl => (hd + 1) %:: tl
  | .fs n, hd %:: tl => hd %:: inc_vec n tl

theorem inc_vec.eq_set {idx : Fin2 n} {s : Vec Nat n}
    : inc_vec idx s = s.set idx (s.lookup idx |>.succ) :=
  match idx, s with
  | .fs _, hd %:: _ => by
    dsimp [inc_vec, Vec.set, Vec.lookup]
    rw [eq_set]
  | .fz,   hd %:: _ => rfl

def inc : {r : RegTree} → r.toIdx → r.toStore → r.toStore
  | .lf _, idx, str => inc_vec idx str
  | .br _ _, .inl search, ⟨a, b⟩ => ⟨inc search a, b⟩
  | .br _ _, .inr search, ⟨a, b⟩ => ⟨a, inc search b⟩

theorem inc.eq_set {r : RegTree} {idx : r.toIdx} {s : r.toStore}
    : inc idx s = r.set s idx (r.lookup s idx |>.succ) :=
  match r, s, idx with
  | .lf _, s, idx => inc_vec.eq_set
  | .br _ _, ⟨l, r⟩, .inl idx
  | .br _ _, ⟨l, r⟩, .inr idx => by
    dsimp [inc, RegTree.set, RegTree.lookup]
    rw [←eq_set]

def dec_vec {r} : Fin2 r → Vec Nat r → Option (Vec Nat r)
  | .fz, 0 %:: tl => .none
  | .fz, hd + 1 %:: tl => .some (hd %:: tl)
  | .fs n, hd %:: tl => dec_vec n tl |>.map (.cons hd)

theorem dec_vec.eq_set {idx : Fin2 n} {s : Vec Nat n}
    (h : dec_vec idx s = some z)
    : z = s.set idx (s.lookup idx |>.pred) :=
  match n, s, idx with
  | _+1, 0   %:: tl, .fz   => Option.noConfusion h
  | _+1, n+1 %:: tl, .fz   => by simp_all [dec_vec, Vec.set, Vec.lookup]
  | _+1, hd  %:: tl, .fs _ => by
    simp_all only [dec_vec, Option.map_eq_some', Vec.set, Vec.lookup]
    rcases h with ⟨_, ih, rfl⟩
    exact (Vec.cons.injEq _ _ _ _).mpr ⟨rfl, dec_vec.eq_set ih⟩

def dec : {r : RegTree} → r.toIdx → r.toStore → Option r.toStore
  | .lf _, idx, str => dec_vec idx str
  | .br _ _, .inl search, ⟨a, b⟩ => (dec search a).map (⟨·, b⟩)
  | .br _ _, .inr search, ⟨a, b⟩ => (dec search b).map (⟨a, ·⟩)

def dec.eq_set {r : RegTree} {idx : r.toIdx} {z s : r.toStore}
    (h : dec idx s = some z)
    : z = r.set s idx (r.lookup s idx |>.pred) :=
  match r, idx with
  | .lf _, idx => dec_vec.eq_set h
  | .br _ _, .inl _ | .br _ _, .inr _ => by
    simp_all only [dec, Option.map_eq_some', RegTree.set, RegTree.lookup]
    rcases h with ⟨_, ih, rfl⟩
    refine (Prod.mk.injEq _ _ _ _).mpr ⟨?_, ?_⟩
    any_goals rfl
    exact dec.eq_set ih

theorem dec_vec_none_iff_lookup_z
     {idx : Fin2 n} {s : Vec _ _}
    : (dec_vec idx s = none) ↔ s.lookup idx = 0 :=
  match idx, s with
  | .fz,   0 %:: _ | .fz,   n+1 %:: _ => by
    simp [dec_vec, Vec.lookup]
  | .fs _, hd %:: _  => by
    simp only [dec_vec, Option.map_eq_none', Vec.lookup]
    exact dec_vec_none_iff_lookup_z

theorem dec_none_iff_lookup_z
    {r : RegTree} {idx : r.toIdx} {s : r.toStore}
    : (dec idx s = none) ↔ r.lookup s idx = 0 :=
  match r, idx with
  | .lf _, idx => dec_vec_none_iff_lookup_z
  | .br _ _, .inl _
  | .br _ _, .inr _ => by
    simp only [dec, Option.map_eq_none', RegTree.lookup]
    exact dec_none_iff_lookup_z

def Config.step (state : Config r L) : Option $ Config r L :=
  let ⟨regs, state⟩ := state
  match machine state with
  | .inc r l => .some ⟨inc r regs, l⟩
  | .dec r l1 l2 =>
    match dec r regs with
    | .some regs => .some ⟨regs, l1⟩
    | .none      => .some ⟨regs, l2⟩
  | .hlt => .none

theorem Config.step.none_hlt [Fintype2 L] {inM : RegMachine r L}
    (h : RegMachine.Config.step inM ⟨view, s⟩ = none)
    : inM s = .hlt :=
  match heq : inM s with
  | .hlt => rfl
  | .inc _ _ | .dec _ _ _ => by
    simp only [Config.step, heq] at h
    <;> split at h
    <;> exact Option.noConfusion h


def Config.step_n (state : Config r L) : Nat → Option (Config r L)
  | 0 => state
  | n+1 => (state.step machine).bind (step_n · n)

@[simp]
theorem Config.step_n.zero {s : Config r L} : s.step_n m 0 = some s := rfl

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

def trans {m : RegMachine _ L} : StepsTo m a b → StepsTo m b c → StepsTo m a c
  | ⟨w₁, p₁⟩, ⟨w₂, p₂⟩ =>
    ⟨w₂ + w₁, by simp only [Config.step_n.add, p₁, Option.some_bind, p₂] ⟩

instance {m : RegMachine r L} : Trans (StepsTo m) (StepsTo m) (StepsTo m) := ⟨trans⟩

def refl : StepsTo machine a a := ⟨0, rfl⟩

end StepsTo

/-- Terminates with -/
def TW (start term : Config r L) : Prop :=
  ∃ n, start.step_n machine n = .some term ∧ term.step machine = .none

namespace TW

def trans {m : RegMachine _ L} : StepsTo m a b → TW m b c → TW m a c
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

class Computable (f : Vec Nat ina → Vec Nat outa) where
  {L : _} {r : _} [inst : Fintype2 L]
  (m : RegMachine (.br (.lf outa) $ .br (.lf ina) r) L)
  (startins : _)
  (p : ∀ inp, ∃ eregs endins, m.TW
      ⟨⟨.zero, ⟨inp, .zero⟩⟩, startins⟩ ⟨⟨f inp, eregs⟩, endins⟩)

attribute [instance] Computable.inst

structure Pfn (n m : Nat) where
  carrier : Vec Nat n → Vec Nat m → Prop
  nomulti : ∀ x y z, carrier x y → carrier x z → y = z

class Pfn.Computable (f : Pfn ina outa) where
  {L : _} {r : _} [inst : Fintype2 L]
  (m : RegMachine (.br (.lf outa) $ .br (.lf ina) r) L)
  (startins : _)
  (proof : ∀ inp out, ∃ eregs endins, f.carrier inp out
    ↔ m.TW ⟨⟨.zero, ⟨inp, .zero⟩⟩, startins⟩ ⟨⟨out, eregs⟩, endins⟩)

attribute [instance] Pfn.Computable.inst

