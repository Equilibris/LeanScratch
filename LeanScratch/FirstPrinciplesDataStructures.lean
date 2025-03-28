import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic

def nApply (motive : Type u) (functor : Type u → Type u) : Nat → Type u
  | 0 => motive
  | n+1 => functor (nApply motive functor n)

inductive ListFunctor (α ρ : Type _) : Type _
  | nil
  | cons (hd : α) (cons : ρ)

namespace ListFunctor
inductive Crystal {base : Type} :
    (n : Nat) →
    nApply base (ListFunctor α) n →
    nApply base (ListFunctor α) n.succ → Prop where
  | base  : Crystal 0 b v
  | nilS  : Crystal (n + 1) .nil .nil
  | consS : Crystal n t₁ t₂ →
    ListFunctor.Crystal (n + 1) (.cons h₁ t₁) (.cons h₁ t₂)

namespace Crystal
def cons
    {obj : (n : ℕ) → nApply Unit (ListFunctor α) n}
    (cryst : ∀ (n : ℕ), ListFunctor.Crystal n (obj n) (obj n.succ))
    (h : obj 1 = ListFunctor.cons hd PUnit.unit)
    : (x : ℕ) → ∃ tl, obj x.succ = ListFunctor.cons hd tl
  | 0 => by
    have := cryst 1
    cases h' : obj 2 <;> simp_all [h', h]
  | n+1 => by
    have ⟨tl', h⟩ := Crystal.cons cryst h n
    have := cryst (n+1)
    cases h' : obj (n+2) <;> simp_all [h', h]
    <;> cases this
    exact ⟨_, rfl⟩

def nil
    {obj : (n : ℕ) → nApply Unit (ListFunctor α) n}
    (cryst : ∀ (n : ℕ), ListFunctor.Crystal n (obj n) (obj n.succ))
    (h : obj 1 = .nil)
    : (x : Nat) → obj x.succ = .nil
  | 0 => by
    have := cryst 1
    cases h' : obj 2 <;> simp_all [h', h]
  | n+1 => by
    have := cryst (n+1)
    cases h' : obj (n+2)
    <;> rw [h', nil cryst h n] at this
    clear h h'
    cases this
end Crystal

def Tight {α} {x : Nat} : nApply Empty (ListFunctor α) x.succ → Prop :=
  (¬∃ x, Crystal _ x ·)
end ListFunctor

structure List' (α : Type _) :=
  bound : Nat
  content : nApply Empty (ListFunctor α) bound.succ
  tightness : ListFunctor.Tight content

def List'.lift : {n : Nat} → nApply Empty (ListFunctor α) n → List' α
  | _+1, .nil => ⟨0, .nil, Empty.elim ∘ Exists.choose⟩
  | n+1, .cons hd tl =>
    let ⟨n, v, tight⟩ := List'.lift tl
    ⟨n+1, .cons hd v, fun ⟨w, p⟩ => by cases p; exact tight ⟨_ , (by assumption)⟩⟩

def List'.cons : α → List' α → List' α
  | hd, ⟨n, tl, tight⟩ => ⟨
    n+1,
    .cons hd tl,
    fun ⟨w, p⟩ => match p with | .consS v => tight ⟨_ , v⟩⟩

def List'.nil : List' α := ⟨0, .nil, Empty.elim ∘ Exists.choose⟩

def List'.dest : List' α → ListFunctor α (List' α)
  | ⟨0, .nil, _⟩ | ⟨_+1, .nil, _⟩ => .nil
  | ⟨_+1, .cons hd tl, _⟩ => .cons hd $ List'.lift tl

/- def List'.ind -/
/-     {motive : List' α → Sort _} -/
/-     (hNil : motive .nil) -/
/-     (hCons : (hd : α) → (x : List' α) → motive x → motive (.cons hd x)) -/
/-     (ls : List' α) -/
/-     : motive ls := -/
/-   let ⟨n, v, tight⟩ := ls -/
/-   dec n v tight -/
/-   where -/
/-     dec (n : Nat) (v : nApply _ _ n.succ) tight := match n, v with -/
/-     | 0, .nil => hNil -/
/-     | n+1, .nil => False.elim $ tight ⟨.nil , .nilS⟩ -/
/-     | n+1, .cons hd tl => hCons hd (List'.lift tl) sorry -/

/- instance : Equiv (List α) (List' α) where -/
/-   toFun := sorry -/


structure CoList (α : Type _) where
  obj : (n : Nat) → nApply Unit (ListFunctor α) n
  cryst : ∀ n, ListFunctor.Crystal n (obj n) (obj n.succ)

-- This will in the end be the only efficent way to walk the graph sadly, and a bit pathalogically
def CoList.destN (o : CoList α) : nApply (CoList α) (ListFunctor α) n :=
  let ⟨obj, cryst⟩ := o
  let struct := obj n
  walker struct
where
  walker : {k : Nat} → nApply _ _ k → nApply _ _ k
  | 0, _ => sorry
  | n+1, .nil => sorry
  | n+1, .cons _ _ => sorry

def CoList.dest (o : CoList α) : ListFunctor α (CoList α) :=
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
        clear *-this
        exact match this with | .consS x => x
    ⟩

def CoList.corec.impl
    (f : ρ → ListFunctor α ρ) (content : ρ) 
    : (x : ℕ) → nApply Unit (ListFunctor α) x
  | 0 => .unit
  | _+1 => match f content with
    | .nil => .nil
    | .cons hd tl => .cons hd (impl f tl _)

-- TODO: Add the concept of an indexer type to make co-rec generation much faster (hopefully)
-- No, turns out this is a fundemental failure of progressive generation.
-- This can be fixed though, or at least made linear which should make scaling less insane.
-- To do this we need eacg approximation to become exponentially better than the last.
-- With this done the amortized cost will become 𝓞(n)

def CoList.corec.proof : ∀ (x : ℕ), ListFunctor.Crystal x (impl f v x) (impl f v x.succ)
  | 0 => .base
  | n+1 => by
    dsimp [corec.impl]
    match f v with
    | .nil      => exact .nilS
    | .cons _ _ => exact .consS $ corec.proof n

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


def takeList (l : CoList α) : Nat → List α
  | 0 => []
  | n+1 =>
    match l.dest with
    | .nil => []
    | .cons hd tl => hd :: takeList tl n

#reduce takeList (CoList.corec (fun x => .cons x x.succ) 0) 103

