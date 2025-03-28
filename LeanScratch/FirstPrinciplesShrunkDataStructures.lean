inductive ListFunctor (α ρ : Type _) : Type _
  | nil
  | cons (hd : α) (cons : ρ)

namespace ListFunctor
inductive Crystal {base : Type u} :
    {n : Nat} →
    {m : Nat} →
    n.repeat (ListFunctor.{u} α) base →
    m.repeat (ListFunctor.{u} α) base → Prop where
  | base  : @Crystal _ _ (0    ) (m + 1) b v
  | nilS  : @Crystal _ _ (n + 1) (m + 1) .nil .nil
  | consS : @Crystal _ _ (n    ) (m    ) t₁   t₂ →
            @Crystal _ _ (n + 1) (m + 1) (.cons h₁ t₁) (.cons h₁ t₂)

namespace Crystal
def cons
    {obj : (n : Nat) → n.repeat (ListFunctor α) Unit}
    (cryst : ∀ (n : Nat), ListFunctor.Crystal (obj n) (obj n.succ))
    (h : obj 1 = ListFunctor.cons hd PUnit.unit)
    : (x : Nat) → ∃ tl, obj x.succ = ListFunctor.cons hd tl
  | 0 => by
    have := cryst 1
    cases h' : obj 2 <;> simp_all [h', h] <;> cases this
    exact ⟨_, rfl⟩

  | n+1 => by
    have ⟨tl', h⟩ := Crystal.cons cryst h n
    have := cryst (n+1)
    cases h' : obj (n+2) <;> simp_all [h', h]
    <;> cases this
    exact ⟨_, rfl⟩

def nil
    {obj : (n : Nat) → n.repeat (ListFunctor α) Unit}
    (cryst : ∀ (n : Nat), ListFunctor.Crystal (obj n) (obj n.succ))
    (h : obj 1 = .nil)
    : (x : Nat) → obj x.succ = .nil
  | 0 => by
    have := cryst 1
    cases h' : obj 2 <;> simp_all [h', h]
  | n+1 => by
    have := cryst (n+1)
    cases h' : obj (n+2) <;> rw [h', nil cryst h n] at this
    cases this
end Crystal
end ListFunctor

structure CoList (α : Type u) : Type u where
  obj : (n : Nat) → n.repeat (ListFunctor α) PUnit
  cryst : ∀ n, ListFunctor.Crystal (obj n) (obj n.succ)

namespace CoList
def dest (o : CoList α) : ListFunctor α (CoList α) :=
  let ⟨obj, cryst⟩ := o
  match h₁ : obj 1 with
  | .nil => .nil
  | .cons hd .unit =>
    .cons hd ⟨
      (fun x => match h₂ : obj x.succ with
      | .cons _ tl => tl
      | .nil => ListFunctor.Crystal.cons cryst h₁ x
          |> Exists.choose_spec 
          |>.symm.trans h₂
          |> ListFunctor.noConfusion
      ),
      fun n => by
        dsimp
        split
        <;> rename_i heq₁
        case h_2 =>
          exact ListFunctor.Crystal.cons cryst h₁ n
            |> Exists.choose_spec
            |>.symm.trans heq₁
            |> ListFunctor.noConfusion 
        have ⟨_, p⟩ := ListFunctor.Crystal.cons cryst h₁ n.succ 
        split
        <;> rename_i heq₂
        case h_2 =>
          exact ListFunctor.noConfusion $ p.symm.trans heq₂
        have := cryst n.succ
        rw [heq₁, heq₂] at this
        clear h₁
        exact match this with | .consS x => x
    ⟩

def corec.impl
    {α : Type v} {ρ : Type u}
    (f : ρ → ListFunctor α ρ) (content : ρ)
    : (x : Nat) → x.repeat (ListFunctor α) PUnit.{v+1}
  | 0 => .unit
  | _+1 => match f content with
    | .nil => .nil
    | .cons hd tl => .cons hd (impl f tl _)

-- TODO: Add the concept of an indexer type to make co-rec generation much faster (hopefully)
-- No, turns out this is a fundemental failure of progressive generation.
-- This can be fixed though, or at least made linear which should make scaling less insane.
-- To do this we need eacg approximation to become exponentially better than the last.
-- With this done the amortized cost will become 𝓞(n)

def corec.proof : ∀ (x : Nat), ListFunctor.Crystal (impl f v x) (impl f v x.succ)
  | 0 => .base
  | n+1 => by
    dsimp [corec.impl]
    match f v with
    | .nil      => exact .nilS
    | .cons _ _ => exact .consS $ corec.proof n

def corec {α : Type v} {ρ : Type u} (f : ρ → ListFunctor α ρ) (v : ρ) : CoList α :=
  ⟨corec.impl f v, corec.proof⟩

-- This will be the base of a quotient for efficent generators
structure PerfBase (α : Type u) : Type (max u v + 1) where
  {dom   : Type v}
  (init  : dom)
  (coalg : dom → ListFunctor α dom)

namespace PerfBase

def dest : PerfBase α → ListFunctor α (PerfBase α)
  | ⟨init, coalg⟩ => match coalg init with
    | .nil => .nil
    | .cons hd tl => .cons hd ⟨tl, coalg⟩

/- inductive Bisim.Invariant' (R : PerfBase α → PerfBase α → Prop) : ListFunctor α (PerfBase α) → ListFunctor α (PerfBase α) → Prop -/
/-   | cons : R t₁ t₂ → Invariant' R (.cons h t₁) (.cons h t₂) -/
/-   | nil : Invariant' R .nil .nil -/

/- def Bisim.Invariant (R : PerfBase α → PerfBase α → Prop) (a b : PerfBase α) : Prop := -/
/-   Invariant' R a.dest b.dest -/

inductive Bisim.Invariant (R : PerfBase α → PerfBase α → Prop) : PerfBase α → PerfBase α → Prop
  | cons : l₁.dest = (.cons h t₁) → l₂.dest = (.cons h t₂) → R t₁ t₂ → Invariant R l₁ l₂
  | nil : l₁.dest = .nil → l₂.dest = .nil → Invariant R l₁ l₂

abbrev Bisim.Is (R : PerfBase α → PerfBase α → Prop) : Prop :=
  ∀ {x y}, R x y → Bisim.Invariant R x y

def Bisim (a b : PerfBase α) : Prop :=
  ∃ R, Bisim.Is R ∧ R a b

theorem Bisim.unfold {α}: @Bisim.Is α Bisim := fun ⟨R, h_is, h_Rst⟩ =>
  match h_is h_Rst with
  | .cons hA hB h => .cons hA hB ⟨R, h_is, h⟩
  | .nil hA hB => .nil hA hB

theorem Bisim.refl : Bisim a a := by
  refine ⟨Eq, ?_, rfl⟩
  rintro x _ rfl
  cases h : x.dest
  · exact .nil h h
  · exact .cons h h rfl

theorem Bisim.symm (h : Bisim a b) : Bisim b a := by
  rcases h with ⟨rel, relIsBisim, rab⟩
  refine ⟨fun a b => rel b a, fun holds => ?_, rab⟩
  cases relIsBisim holds
  case cons h eqa eqb => exact .cons eqb eqa h
  case nil eqa eqb => exact .nil eqb eqa

theorem Bisim.trans {a b c : PerfBase α} (h_ab : Bisim a b) (h_bc : Bisim b c) :
    Bisim a c := by
  refine ⟨(fun s t => ∃ u, Bisim s u ∧ Bisim u t), fun ⟨m, hx, hy⟩ => ?_, ⟨_, h_ab, h_bc⟩⟩
  cases hx.unfold <;> cases hy.unfold
  any_goals (simp_all only; done)
  case cons hx hl hm₁ _ _ _ hy hm₂ hr =>
    obtain ⟨rfl, rfl⟩ := (ListFunctor.cons.injEq _ _ _ _).mp $ hm₁.symm.trans hm₂
    exact .cons hl hr ⟨_, hx, hy⟩
  case nil hl _ hm hr => 
    exact .nil hl hr

instance instSetoid α : Setoid (PerfBase α) where
  r := Bisim
  iseqv := {
    refl  := fun _ => Bisim.refl
    symm  := Bisim.symm
    trans := Bisim.trans
  }

def Perf (α : Type _) := Quotient (instSetoid α)


