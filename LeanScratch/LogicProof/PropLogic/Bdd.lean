import LeanScratch.Fin2
import LeanScratch.LogicProof.PropLogic.Formula

namespace PLogic

inductive Bdd.Base (Var : Type) : Nat → Type
  | nil : Base _ 0
  | bot (v : Bool) (rest : Base Var n) : Base Var n.succ
  | node (v : Var) (l r : Fin2 n) (rest : Base Var n) : Base Var n.succ

namespace Bdd.Base

def get : Base Var n → Fin2 n → (n : Nat) × Base Var n.succ
  | x, .fz => ⟨_, x⟩
  | .bot _ rest, .fs idx      => rest.get idx
  | .node _ _ _ rest, .fs idx => rest.get idx

theorem get_le
    : {inp : Bdd.Base V n} → {idx : Fin2 n} → (inp.get idx).fst.succ ≤ n
  | _, .fz => by simp [Nat.succ_eq_add_one, get]
  | .bot _ rest, .fs i
  | .node _ _ _ rest, .fs i => calc
    (rest.get i).fst + 1 ≤ _     := get_le
    _                    ≤ _ + 1 := Nat.le_add_right _ _

theorem get_le'
    {inp : Bdd.Base V n} {idx : Fin2 n} (h : inp.get idx = ⟨n₁, v⟩)
    : n₁.succ ≤ n := by
  have := (Sigma.eta _).trans h
  injections feq seq
  rw [←feq]
  exact get_le (inp := inp) (idx := idx)

@[elab_as_elim]
def Bdd.Base.ind
    {motive : (n : _) → Bdd.Base Var n.succ → Sort u}
    (hBaseHolds : {n : _} → (rst : Base Var n) → (b : _) → motive _ (.bot b rst))
    (hNode      :
      {n : _} →
      (rst : Base Var n) →
      (v l r : _) →
      (ihl : motive _ (rst.get l).snd) →
      (ihr : motive _ (rst.get r).snd) →
      motive _ (.node v l r rst))
    : {n : Nat} → (t : Bdd.Base Var (n + 1)) → motive n t := fun {n} t =>
  match t with
  | .bot v rst => hBaseHolds _ _
  | .node v l r rst =>
    match hl : rst.get l, hr : rst.get r with
    | ⟨n₁, l⟩, ⟨n₂, r⟩ =>
      have : n₁ < n := get_le' hl
      have : n₂ < n := get_le' hr
      have l := ind hBaseHolds hNode l
      have r := ind hBaseHolds hNode r
      hNode _ _ _ _ (hl.symm.rec l) (hr.symm.rec r)
termination_by n => n

inductive Equiv : Base Var n → Base Var m → Prop
  | nil : Equiv .nil .nil
  | bot : Equiv r₁ r₂ → Equiv (.bot v r₁) (.bot v r₂)
  | node
      (hLEq : Equiv (rst₁.get l₁).snd (rst₁.get l₂).snd)
      (hREq : Equiv (rst₂.get r₁).snd (rst₂.get r₂).snd)
      : Equiv (.node v l₁ r₁ rst₁) (.node v l₂ r₂ rst₂)

abbrev ifte (v t f : Prop) :=
  (v → t) ∧ (¬v → f)

/- def Denote (Base : Var → Prop) : Bdd.Base Var n → Prop -/
/-   | .nil => False -/
/-   | .bot b _ => b -/
/-   | .node v l r rst => ifte (Base v) () -/

inductive Denote (Base : Var → Prop) : Bdd.Base Var n → Prop
  | botT  : Denote Base (.bot .true _)
  | nodeT :  Base v → Denote Base (rst.get l).snd → Denote Base (.node v l r rst)
  | nodeF : ¬Base v → Denote Base (rst.get r).snd → Denote Base (.node v l r rst)

@[simp]
def Denote.bot : Denote B (.bot v rst) = v := 
  propext ⟨
    fun | botT => rfl,
    fun h => h.symm.rec .botT
  ⟩

@[simp]
def Denote.node :
    Denote B (.node v l r rst) =
    ifte (B v) (Denote B (rst.get l).snd) (Denote B (rst.get r).snd) :=
  propext ⟨
    fun
      | .nodeT b v
      | .nodeF b v => by simp_all [ifte],
    fun ⟨l, r⟩ => by
      by_cases h : B v
      · exact .nodeT h (l h)
      · exact .nodeF h (r h)
  ⟩

end Base

abbrev Base.CodesFor (v : Formula Var) (t : Bdd.Base Var n) : Prop :=
  v.denote = t.Denote

def Base.neg : Base Var n → Base Var n
  | .nil => .nil
  | .bot x rst => .bot x.not rst.neg
  | .node v l r rst => .node v l r rst.neg

theorem Base.neg.correct {t : Base Var (n + 1)} (h : CodesFor v t) : CodesFor v.neg t.neg := by
  ext base
  apply (Function.funext_iff.mp · base) at h
  induction t using Bdd.Base.ind generalizing v
  · simp [Denote, neg, Formula.denote, h] at h ⊢
  case hNode rst v' l r ihl ihr =>
    simp [Nat.succ_eq_add_one, neg] at *
    by_cases h' : base v'
    <;> simp_all [ifte, h]
    · specialize ihl h
      sorry
    · specialize ihr h
      sorry

