import LeanScratch.Fin2
import LeanScratch.LogicProof.PropLogic.Formula

inductive Bdd.Base (Var : Type) : Nat → Type
  | nil : Base Var 0
  | node (v : Var) (l r : Bool ⊕ Fin2 n) (rest : Base Var n) : Base Var n.succ

/- example {α : Type v} {β : α → Type u} : (x : α) → β x := sorry -/

def Bdd.Base.get : Base Var n → Fin2 n → Sigma (Base Var)
  | x, .fz => ⟨_, x⟩
  | .node _ _ _ rest, .fs idx => rest.get idx

def Bdd.Base.get' : Base Var n → {x : Fin2 n} → Base Var (n - x.toNat)
  | x, .fz => x
  | .node _ _ _ rest, .fs idx =>
    sorry
    /- let x := rest.get' idx -/
    /- sorry -/

theorem Bdd.Base.get_le
    : {inp : Bdd.Base V n} → {idx : Fin2 n} → (inp.get idx).fst ≤ n
  | _, .fz => by simp only [get, le_refl]
  | .node _ _ _ rest, .fs i => calc
    (rest.get i).fst ≤ _     := get_le
    _                ≤ _ + 1 := Nat.le_add_right _ _

/- def Bdd.equiv : Base Var n → Base Var m → Prop -/

inductive Bdd.Equiv : Base Var n → Base Var m → Prop
  | nil : Equiv .nil .nil
  | bothStep
      (hLEq : Equiv (rst₁.get l₁).snd (rst₁.get l₂).snd)
      (hREq : Equiv (rst₂.get r₁).snd (rst₂.get r₂).snd)
      : Equiv (.node v (.inr l₁) (.inr r₁) rst₁) (.node v (.inr l₂) (.inr r₂) rst₂)
  | lStep
      (hLEq : Equiv (rst₁.get l₁).snd (rst₁.get l₂).snd)
      : Equiv (.node v (.inr l₁) (.inl b) rst₁) (.node v (.inr l₂) (.inl b) rst₂)
  | rStep
      (hREq : Equiv (rst₂.get r₁).snd (rst₂.get r₂).snd)
      : Equiv (.node v (.inl b) (.inr r₁) rst₁) (.node v (.inl b) (.inr r₂) rst₂)

elab "require_defined" n:ident : tactic => fun stx => (do
  let ctx ← Lean.MonadLCtx.getLCtx
  let v ← ctx.findDeclM? fun decl => do
    if decl.userName = n.getId then return .some Unit.unit
    else                            return .none

  match v with
  | .some _ => pure ()
  | .none => throwErrorAt n s!"{n} is not defined"
)

/-

def Bdd.Equiv.dec [DecidableEq Var] : (x : Base Var n) → (y : Base Var m) → Decidable (Bdd.Equiv x y)
  | .nil, .nil => .isTrue (.nil)
  | .node v₁ l₁ r₁ rst₁, .node v₂ l₂ r₂ rst₂ =>
    -- might be better to write in tactic mode...
    if h : v₁ = v₂ then by
      match l₁, l₂ with
      | .inl .true, .inl .false | .inl .false, .inl .true 
      | .inr _, .inl _ | .inl _, .inr _ => exact .isFalse (fun x => by cases x)

      | .inl .true, .inl .true
      | .inl .false, .inl .false
      | .inr li₁, .inr li₂ =>
      match r₁, r₂ with
      | .inl .true, .inl .false | .inl .false, .inl .true 
      | .inr _, .inl _ | .inl _, .inr _ => exact .isFalse (fun x => by cases x)
      | .inl .true, .inl .true
      | .inl .false, .inl .false
      | .inr ri₁, .inr ri₂ =>
        all_goals skip
        any_goals require_defined li₁
        /- any_goals ( require_defined li₁; have ldec := dec (rst₁.get li₁).snd (rst₂.get li₂).snd) -/
        sorry


    else
      .isFalse (fun x => by cases x <;> exact h rfl)
    /- ∧ (match l₁, l₂ with -/
    /-   | .inr idx₁, .inr idx₂ => -/
    /-     Bdd.Equiv (rst₁.get idx₁).snd (rst₂.get idx₂).snd -/
    /-   | .inl .true, .inl .true -/
    /-   | .inl .false, .inl .false => True -/
    /-   | _, _ => False) -/
    /- ∧ (match r₁, r₂ with -/
    /-   | .inr idx₁, .inr idx₂ => -/
    /-     Bdd.Equiv (rst₁.get idx₁).snd (rst₂.get idx₂).snd -/
    /-   | .inl .true, .inl .true -/
    /-   | .inl .false, .inl .false => True -/
    /-   | _, _ => False) -/
  | .node _ _ _ _, .nil
  | .nil, .node _ _ _ _ => .isFalse (fun x => by cases x)
/- termination_by n -/
/- decreasing_by -/
/- all_goals { -/
/-   simp_wf -/
/-   apply Nat.lt_succ_of_le -/
/-   exact Bdd.Base.get_le -/
/- } -/
-/



