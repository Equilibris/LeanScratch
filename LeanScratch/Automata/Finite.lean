import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset

namespace Automata.Finite

class Langauge (T : Sort _) (α : outParam (Sort _)) := Matches : T → List α → Prop

abbrev iso {A B} (a : A) (b : B) [i₁ : Langauge A α] [i₂ : Langauge B α] := ∀ s, i₁.Matches a s ↔ i₂.Matches b s
scoped infix:20 " ≅ " => iso

namespace iso

theorem isoRefl [Langauge L α] (a : L) : a ≅ a := by
  intro l
  exact Eq.to_iff rfl

theorem isoSymm [Langauge L₁ α] [Langauge L₂ α] {a : L₁} {b : L₂} (h : a ≅ b) : b ≅ a := by
  intro l
  exact iff_comm.mp (h l)

theorem isoTrans
  [Langauge L₁ α] [Langauge L₂ α] [Langauge L₃ α] {a : L₁} {b : L₂} {c : L₃}
  (h₁ : a ≅ b) (h₂ : b ≅ c) : a ≅ c := by
  intro l
  exact Iff.trans (h₁ l) (h₂ l)
end iso

/- instance { α } -/
/-   [Langauge L₁ α] [Langauge L₂ α] [Langauge L₃ α] -/
/-   : Trans (@iso α L₁ L₂) (@iso α L₂ L₃) (@iso α L₁ L₃) := ⟨isoTrans⟩ -/

inductive Regex (α : Sort _)
  | val (v : α)
  | concat (a b : Regex α)
  | union  (a b : Regex α)
  | star   (a : Regex α)
  | ε

namespace Regex
inductive Matches {α : Sort _} : Regex α → List α → Prop
  | val : Matches (.val v) [v]
  | concat : Matches a la → Matches b lb → Matches (.concat a b) (la ++ lb)
  | unionL : Matches a la → Matches (.union a b) la
  | unionR : Matches a la → Matches (.union b a) la
  | starε : Matches (.star a) []
  | star : Matches a la → Matches (.star a) lrest → Matches (.star a) (la ++ lrest)
  | ε : Matches (.ε) []

instance : Langauge (Regex α) α := ⟨Matches⟩

end Regex

structure NFA (σ : Sort*) where
  (Q : Sort _)
  [QisFin : Fintype Q]

  (Δ : Q → σ → Q → Prop)
  (s : Q)
  (F : Set Q)

attribute [instance] NFA.QisFin

namespace NFA

abbrev Matches.from (v : NFA σ) (s : v.Q) : List σ → Prop
  | [] => s ∈ v.F
  | hd :: tl => ∃ next, v.Δ s hd next → Matches.from v next tl
abbrev Matches (v : NFA σ) (str : List σ) : Prop := Matches.from v v.s str

instance : Langauge (NFA α) α := ⟨Matches⟩

end NFA

structure DFA (σ) where
  base : NFA σ
  isFunc : ∀ q curr next₁ next₂, base.Δ q curr next₁ ∧ base.Δ q curr next₂ → next₁ = next₂

instance : Langauge (DFA σ) σ := ⟨fun x => NFA.Matches x.base⟩

structure NFAε (σ) where
  base : NFA σ
  T : Q → Q → Prop

namespace NFAε

abbrev Matches.from (v : NFAε σ) (s : v.base.Q) : List σ → Prop
  | [] => s ∈ v.base.F
  | hd :: tl => ∃ next, (v.base.Δ s hd next → Matches.from v next tl) ∨ (∃ next', v.T s next → v.base.Δ next hd next' → Matches.from v next' tl)
abbrev Matches (v : NFAε σ) (str : List σ) : Prop := Matches.from v v.base.s str

instance : Langauge (NFAε α) α := ⟨Matches⟩

end NFAε

def NFA.allTrans (v : NFA σ) (state : Set v.Q) (pos : σ) : Set v.Q := setOf fun x => ∃ s ∈ state, v.Δ s pos x

theorem NFA_Is_DFA (base : NFA.{_, u + 1} σ) : ∃ h : DFA.{_, u + 1} σ, base ≅ h := by
  exists {
    base := ({
        Q := Set base.Q
        Δ := fun prev pos next => base.allTrans prev pos = next
        s := {base.s}
        F := setOf fun x => ∃ s ∈ x, s ∈ base.F
      })
    isFunc := by simp only [and_imp, forall_apply_eq_imp_iff, forall_eq', implies_true]
  }
  intro s
  cases s
  <;> simp only [Langauge.Matches, NFA.Matches, NFA.Matches.from, Set.mem_setOf_eq,
    Set.mem_singleton_iff, exists_eq_left]
  case cons hd tl =>
    constructor
    <;> rintro ⟨next, p⟩
    · use base.allTrans {base.s} hd
      intro h
      induction tl
      · simp_all [Langauge.Matches, NFA.Matches, NFA.Matches.from]
        use next
        simp [NFA.allTrans]
        sorry
      · sorry
      /- simp only [Langauge.Matches, NFA.Matches] at ih -/
    · sorry
  /- exists ({ -/
  /-   Q := base.base.Q -/
  /-   QisFin := base.base.QisFin -/
  /-   Δ := fun prev σ next => -/
  /-     ∃ i, Relation.ReflTransGen base.T prev i → base.base.Δ i σ next -/
  /-   s := base.base.s -/
  /-   F := base.base.F -/
  /- }) -/
  /- unfold iso -/
  /- introv -/
  /- cases s -/
  /- · constructor -/
  /-   <;> intro h -/
  /-   <;> simp_all only [Langauge.Matches] -/
  /- case cons hd tl => -/
  /-   simp [Langauge.Matches, NFA.Matches, NFAε.Matches, NFA.Matches.from, NFAε.Matches.from] at * -/
  /-   constructor -/
  /-   <;> rintro ⟨next, p⟩ -/
  /-   · use next -/
  /-     introv -/
  /-     sorry -/

  /-   · sorry -/

theorem NFAε_Is_NFA (base : NFAε.{_, _, u + 1} σ) : ∃ h : NFA.{_, u} σ, base ≅ h := by
  exists ({
    Q := base.base.Q
    QisFin := base.base.QisFin
    Δ := fun prev σ next =>
      ∃ i, Relation.ReflTransGen base.T prev i → base.base.Δ i σ next
    s := base.base.s
    F := base.base.F
  })
  unfold iso
  introv
  cases s
  · constructor
    <;> intro h
    <;> simp_all only [Langauge.Matches]
  case cons hd tl =>
    simp [Langauge.Matches, NFA.Matches, NFAε.Matches, NFA.Matches.from, NFAε.Matches.from] at *
    constructor
    <;> rintro ⟨next, p⟩
    · use next
      introv
      sorry

    · sorry
end Automata.Finite
