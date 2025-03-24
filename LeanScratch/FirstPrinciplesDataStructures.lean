import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic

def nApply (motive : Sort _) (functor : Sort _ → Sort _) : Nat → Sort _
  | 0 => functor motive
  | n+1 => functor (nApply motive functor n)

inductive ListFunctor (α ρ : Type _) : Type _
  | nil
  | cons (hd : α) (cons : ρ)

namespace ListFunctor
inductive Crystal {base : Type} :
    (n : Nat) →
    nApply base (ListFunctor α) n →
    nApply base (ListFunctor α) n.succ → Prop where
  | nilZ  : Crystal 0 .nil .nil
  | nilS  : Crystal (n + 1) .nil .nil
  | consZ : Crystal 0 (.cons h₁ z) (.cons h₁ tl)
  | consS : Crystal n t₁ t₂ →
    ListFunctor.Crystal (n + 1) (.cons h₁ t₁) (.cons h₁ t₂)

namespace Crystal
def cons
    {obj : (n : ℕ) → nApply Unit (ListFunctor α) n}
    (cryst : ∀ (n : ℕ), ListFunctor.Crystal n (obj n) (obj n.succ))
    (h : obj 0 = ListFunctor.cons hd PUnit.unit)
    : (x : ℕ) → ∃ tl, obj x.succ = ListFunctor.cons hd tl
  | 0 => by
    have := cryst 0
    cases h' : obj 1
    <;> rw [h', h] at this
    <;> clear h h'
    <;> cases this
    exact ⟨_, rfl⟩
  | n+1 => by
    have ⟨tl', h⟩ := Crystal.cons cryst h n
    have := cryst (n+1)
    cases h' : obj (n+2)
    <;> rw [h', h] at this
    <;> clear h h'
    <;> cases this
    exact ⟨_, rfl⟩

def nil
    {obj : (n : ℕ) → nApply Unit (ListFunctor α) n}
    (cryst : ∀ (n : ℕ), ListFunctor.Crystal n (obj n) (obj n.succ))
    (h : obj 0 = .nil)
    : (x : Nat) → obj x.succ = .nil
  | 0 => by
    have := cryst 0
    cases h' : obj 1
    <;> rw [h', h] at this
    clear h h'
    cases this
  | n+1 => by
    have := cryst (n+1)
    cases h' : obj (n+2)
    <;> rw [h', nil cryst h n] at this
    clear h h'
    cases this
end Crystal

def Tight {α} : {x : Nat} → nApply Empty (ListFunctor α) x → Prop
  | 0, _ => True
  | n+1, y => ¬∃ x, Crystal n x y

end ListFunctor


structure List' (α : Type _) :=
  bound : Nat
  content : nApply Empty (ListFunctor α) bound
  tightness : ListFunctor.Tight content


def List'.cons : α → List' α → List' α
  | hd, ⟨n, tl, tight⟩ => ⟨
    n+1,
    .cons hd tl,
    fun
    | ⟨w, p⟩ => by
      cases p
      · exact Empty.elim (by assumption)
      · apply tight
        exact ⟨_, by assumption⟩
  ⟩

def List'.nil : List' α := ⟨0, .nil, .intro⟩

def List'.dest : List' α → ListFunctor α (List' α)
  | ⟨0, .nil, _⟩ | ⟨_+1, .nil, _⟩ => .nil
  | ⟨n+1, .cons hd tl, _⟩ => .cons hd ⟨n, tl, sorry⟩

/- def List'.rec -/
/-     {motive : List' α → Sort _} -/
/-     (hNil : motive .nil) -/
/-     (hCons : (hd : α) → (x : List' α) → motive x → motive (.cons hd x)) -/
/-     (ls : List' α) -/
/-     : motive ls := -/
/-   let ⟨n, v⟩ := ls -/
/-   dec n v -/
/-   where -/
/-     dec (n : Nat) (v : nApply _ _ n) := match n, v with -/
/-     | 0, .nil => hNil -/
/-     | n+1, .nil => dec n sorry -/
/-     | n+1, .cons _ _ => sorry -/

/- instance : Equiv (List α) (List' α) where -/
/-   toFun := sorry -/


structure CoList (α : Type _) where
  obj : (n : Nat) → nApply Unit (ListFunctor α) n
  cryst : ∀ n, ListFunctor.Crystal n (obj n) (obj n.succ)

def CoList.dest (o : CoList α) : ListFunctor α (CoList α) :=
  let ⟨obj, cryst⟩ := o
  match h₁ : obj 0 with
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
        clear *-this
        exact match this with | .consS x => x
    ⟩

def CoList.corec.impl
    (f : ρ → ListFunctor α ρ) (content : ρ) 
    : (x : ℕ) → nApply Unit (ListFunctor α) x
  | 0 =>
    match f content with
    | .nil => .nil
    | .cons hd _ => .cons hd .unit
  | _+1 => match f content with
    | .nil => .nil
    | .cons hd tl => .cons hd (impl f tl _)

def CoList.corec.proof : ∀ (x : ℕ), ListFunctor.Crystal x (impl f v x) (impl f v x.succ)
  | 0 => by
    dsimp [corec.impl]
    split
    · exact .nilZ
    · exact .consZ
  | n+1 => by
    dsimp [corec.impl]
    split
    · exact .nilS
    · refine .consS $ corec.proof n

def CoList.corec (f : ρ → ListFunctor α ρ) (v : ρ) : CoList α :=
  ⟨corec.impl f v, corec.proof⟩

abbrev TLs (l : List Type) : Type :=
  l.foldl Prod Unit

class SimpleCtorsND (t : Type _) where
  ctors : List $ (arg : Type _) × (arg → t)

class SimpleCasesND (t : Type) extends SimpleCtorsND t where
  cases {motive : t → Type} :
    ((ctors.map
      (fun ⟨args, ctor⟩ => (x : args) → motive (ctor x))).foldl Prod Unit) → ((x : t) → motive x)

