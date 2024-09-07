import Mathlib.Tactic.FinCases
import Mathlib.Data.Set.Basic


structure FSM where
  S : Type
  d : S -> Set S
  A : Set S

example {α} {b c : α → Prop}: (∀ a₁ a₂, b a₁ ∨ c a₂) ↔ ((∀ a, b a) ∨ (∀ a, c a)) := by
  constructor
  · intro h
    apply forall_or_right.mp
    intro ba
    apply forall_or_left.mp
    intro ca
    exact h ba ca

  · intro h a₁ a₂
    cases' h with h h
    · left
      exact h a₁
    · right
      exact h a₂

example : (∃ _ : a, b) ↔ (a ∧ b) := by
  constructor
  · intro ⟨w, p⟩
  · sorry

namespace B1
def IsBisim (fsm : FSM) (R : fsm.S → fsm.S → Prop) : Prop :=
  ∀ s t, R s t →
    (s ∈ fsm.A ↔ t ∈ fsm.A)
    ∧ (∀ s' ∈ fsm.d s, ∃ t' ∈ fsm.d t, R s' t')
    ∧ (∀ t' ∈ fsm.d t, ∃ s' ∈ fsm.d s, R s' t')

def Bisim (fsm : FSM) : fsm.S → fsm.S → Prop :=
  fun s t => ∃ R, IsBisim fsm R ∧ R s t

abbrev allAcc : FSM where
  S := ℕ
  d := fun _ => {}
  A := Set.univ

example : Bisim allAcc 1 2 := by
  let this : Nat → Nat → Prop := fun
    | _, _ => True
  use this
  constructor
  · intro a b h
    simp [this] at h
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    <;> intro h
    <;> simp_all
  · trivial

abbrev oneStep : FSM where
  S := Fin 3
  d := fun
    | 0 => {0}
    | 1 | 2 => {0}
  A := {0}

example : Bisim oneStep 1 2 := by
  use fun
    | 1, 2 | 0, 0 => True
    | _, _ => False
  constructor
  · intro a b v
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    <;> introv h
    <;> fin_cases a
    <;> fin_cases b
    <;> simp_all
  · simp

example : Bisim f a a := by
  use fun a b => a = b
  simp only [and_true]
  intro s t seqt
  simp_all

example (h : Bisim f a b): Bisim f b a := by
  rcases h with ⟨rel, relIsBisim, rab⟩
  use fun a b => rel b a
  simp_all
  intro a₁ b₁ holds
  specialize relIsBisim b₁ a₁ holds
  simp_all only [implies_true, and_self]

example (x : Bisim f a b) (y : Bisim f b c) : Bisim f a c := by
  rcases x with ⟨wx, pix, rab⟩
  rcases y with ⟨wy, piy, rac⟩
  use fun a c => ∃ b, wx a b ∧ wy b c
  constructor
  · intro a c ⟨b, wab, wbc⟩
    specialize pix a b wab
    specialize piy b c wbc
    rcases pix with ⟨aimpb, adriveb, bdrivea⟩
    rcases piy with ⟨bimpc, bdrivec, cdriveb⟩
    simp_all only [true_and]
    constructor
    <;> intro v vmem
    · specialize adriveb v vmem
      rcases adriveb with ⟨wb, wbmem, rvwb⟩
      specialize bdrivec wb wbmem
      rcases bdrivec with ⟨wc, wcmem, rvwc⟩
      use wc
      simp_all only [true_and]
      use wb
    · specialize cdriveb v vmem
      rcases cdriveb with ⟨wb, wbmem, rvwb⟩
      specialize bdrivea wb wbmem
      rcases bdrivea with ⟨wa, wamem, rvwa⟩
      use wa
      simp_all only [true_and]
      use wb
  · use b
end B1

inductive IsEven : Nat → Prop
| zero : IsEven 0
| succ : ∀ n, IsEven n → IsEven (n + 2)

def IsEvenProp (p : Nat → Prop) : Prop :=
  p 0 ∧ (∀ n, p n → p (n + 2))

def IsEven' : Nat → Prop := fun n =>
  ∀ (p : Nat → Prop) (hp : IsEvenProp p), p n

theorem IsEven'_contains_zero : IsEven' 0 := by
  intro p hp
  cases hp
  assumption

theorem IsEven'_ind : IsEven' n → IsEven' (n + 2) := by
  intro h p x
  exact x.2 _ (h p x)

theorem IsEven'_is_IsEven : IsEven n ↔ IsEven' n := by
  constructor
  · intro h
    induction h
    · intro a h
      exact h.1
    case succ _ ih =>
      intro p prop
      exact prop.2 _ (ih p prop)
  · intro h
    apply h
    exact ⟨.zero, .succ⟩

inductive Nat'
  | z
  | s : Nat' → Nat'

def IsNat (p : Type _) : Type _ :=
  p × (p → p)

def Nat'' : Type _ := (p : Type _) → (_ : IsNat p) → p


example : IsEven' 4 := by
  intro p ⟨a, b⟩
  apply b
  apply b
  apply a

