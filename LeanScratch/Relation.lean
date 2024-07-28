import Mathlib.Data.Rel

/- namespace  -/

namespace Relation

section

variable (R : α → α → Prop)

def isTrans  := Rel.comp R R = R
def isRfl    := ∀ a, R a a
def isSymm   := ∀ a, ∀ b, R a b → R b a

def isAntiSymm (R : α → α → Prop) := ∀ a, ∀ b, R a b → R b a → a = b

variable (R : α → β → Prop)

def isInhabited := ∃ a, ∃ b, R a b
def isFull := ∀ a, ∃ b, R a b

def isFn    := ∀ a, ∀ b, R a b → ∀ c, R a c → b = c
def isTotal := ∀ a, ∃! b, R a b

end

theorem isFn' : isFn R = (∀ a, ∀ b, ∀ c, R a b ∧ R a c → b = c) := by
  apply propext
  tauto

abbrev optRel (R : α → β → Prop) : α → Option β → Prop
  | a, none => ¬ ∃ b, R a b
  | a, some b => R a b

abbrev deOpt (R : α → Option β → Prop) (a : α) (b : β) : Prop := R a (some b)

theorem deOpt_optRel : deOpt (optRel R) = R := by
  apply funext₂
  intro a b
  trivial

theorem optRel_isFull { R : α → β → Prop }: isFull (optRel R) := by
  intro a
  by_cases h : ∃ b, R a b
  · rcases h with ⟨w, p⟩
    use some w
  · use none

abbrev graph (f : α → β) (a : α) (b : β) : Prop := f a = b

theorem graph_isTotal : isTotal $ graph f := by
  intro a
  use f a
  constructor
  · trivial
  · intro b holds_ab
    exact holds_ab.symm

theorem full_isInhabited {R : α → β → Prop} [inst : Inhabited α] (full : isFull R) : isInhabited R := by
  unfold isInhabited
  unfold isFull at full
  let a := inst.default
  use a
  rcases full a with ⟨b, p⟩
  use b

theorem full_fn_isTotal (full : isFull R) (fn : isFn R) : isTotal R := by
  intro a
  rcases full a with ⟨w, raw⟩
  use w
  constructor
  · exact raw
  · intro y ray
    exact (fn a w raw y ray).symm

theorem all_total_are_functional : isTotal R → isFn R := by
  intro h a b rab c rac

  rcases h a with ⟨w, ⟨raw, p⟩⟩

  simp at p

  obtain rfl := p c rac
  obtain rfl := p b rab

  rfl

def emptyRel (_ : α) (_ : β) := False

theorem emptyRel_isFull_over_False : isFull $ (@emptyRel False v) := by
  intro a
  contradiction

/- theorem isInhabited_iff_neempty : isInhabited R ↔ R ≠ emptyRel := by -/
/-   constructor -/
/-   · intro h r -/
/-     rcases h with ⟨a, b, rab⟩ -/
/-     rw [r] at rab -/
/-     unfold emptyRel at rab -/
/-     exact rab -/
/-   · intro h -/
/-     unfold emptyRel at h -/
/-     simp at h -/
/-     unfold isInhabited -/
/-     by_contra! -/
/-     sorry -/

theorem emptyRel_is_symm : isSymm $ @emptyRel a a := by
  intro a b
  intro r
  contradiction

theorem emptyRel_is_antiSymm : isAntiSymm $ @emptyRel a a := by
  intro a b
  intro r
  contradiction

theorem emptyRel_is_trans : isTrans $ @emptyRel a a := by
  apply funext₂
  intro a b
  apply propext
  constructor
  · intro r
    rcases r with ⟨w, ⟨p,_⟩⟩
    contradiction

  · intro r
    use a
    trivial

def fullRel (_ : α) (_ : β) := True
def idRel   (a : α) (b : α) := a = b

theorem id_is_symm : isSymm $ @idRel a := by
  intro a b
  intro r
  rw [r]
  rfl

theorem empty_is_antiSymm : isAntiSymm $ @emptyRel a a := by
  intro a b
  intro r
  contradiction

inductive RflTransClosure (R : α → α → Prop) : α → α → Prop
  | base  {a b} (base : R a b) : RflTransClosure R a b
  | rfl   {a} : RflTransClosure R a a
  | trans {a b c} (l1 : RflTransClosure R a b) (l2 : RflTransClosure R b c) : RflTransClosure R a c

theorem RflTransClosure_is_rfl : isRfl $ RflTransClosure R := fun _ => .rfl
theorem RflTransClosure_is_trans : isTrans $ RflTransClosure R := by
  apply funext₂
  intro a b

  apply propext
  constructor
  · intro h
    rcases h with ⟨w, ⟨l1, l2⟩⟩
    exact .trans l1 l2
  · intro h
    use a
    exact ⟨.rfl, h⟩


theorem full_trans_symm_is_rfl (trans : isTrans R) (symm : isSymm R) (full : isFull R) : isRfl R := by
  intro a
  rw [←trans]
  simp [Rel.comp]

  let ⟨w, p⟩ := full a

  use w
  exact ⟨p, symm a w p⟩

abbrev BSeq := Nat → Bool

def R (s1 : BSeq) (s2 : BSeq) : Prop := ∃! n, s1 n ≠ s2 n

def allZeros : BSeq := fun _ => False
def allOnes : BSeq  := fun _ => True

def cons (b : Bool) (tl : BSeq) : BSeq
  | 0 => b
  | .succ n => tl n

/- theorem cons_cancel : R tl tl' ↔ R (cons v tl) (cons v tl') := by -/
/-   constructor -/
/-   · intro h -/
/-     rcases h with ⟨w, ⟨p, unique⟩⟩ -/

/-     use w + 1 -/

/-     simp -/
/-     constructor -/
/-     · simp [cons] -/
/-       by_contra -/
/-       contradiction -/
/-     · intro y h -/
/-       simp at unique -/
/-       have x := unique (y - 1) -/

/-       sorry -/

/-   · intro h -/
/-     rcases h with ⟨w, ⟨p, unique⟩⟩ -/
/-     simp at p -/
/-     simp at unique -/

/-     induction w -/
/-     · contradiction -/
/-     case succ n ih => -/
/-       sorry -/


theorem R_one_True : R allZeros $ cons True allZeros := by
  simp only [R]
  use 0

  constructor
  · simp [allZeros, cons]
  · intro x
    contrapose
    simp only [Decidable.not_not]
    intro h
    cases x
    · contradiction
    · simp [cons, allZeros]

example : R allZeros $ cons False $ cons True allZeros := by
  simp only [R]
  use 1

  constructor
  · simp [allZeros, cons]
  · intro x
    contrapose
    intro h
    simp
    cases x
    · simp [cons, allZeros]
    case succ x =>
      simp [cons, allZeros]
      simp at h
      cases x
      · contradiction
      · simp

theorem R_non_rfl : ¬R a a := by
  by_contra x
  simp [R] at x

def R_tr := RflTransClosure R

example : R_tr allZeros $ cons True $ cons True allZeros := by
  simp only [R_tr]
  apply RflTransClosure.trans
  · apply RflTransClosure.base
    exact R_one_True
  · apply RflTransClosure.base

    simp only [R]
    use 1

    constructor
    · simp [allZeros, cons]
    · intro x
      contrapose
      intro h
      simp
      cases x
      · simp [cons, allZeros]
      case succ x =>
        simp [cons, allZeros]
        simp at h
        cases x
        · contradiction
        · simp

end Relation


