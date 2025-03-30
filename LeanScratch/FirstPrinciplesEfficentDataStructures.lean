import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic

inductive ListFunctor (α ρ : Type _) : Type _
  | nil
  | cons (hd : α) (cons : ρ)

namespace ListFunctor
inductive Crystal {α : Type v} {base : Type (max u v)} :
    {n : Nat} →
    {m : Nat} →
    n.repeat (ListFunctor.{v, max u v} α) base →
    m.repeat (ListFunctor.{v, max u v} α) base → Prop where
  | base  :         @Crystal _ _ (0    ) (m + 1) b v
  | nilS  : n ≤ m → @Crystal _ _ (n + 1) (m + 1) .nil .nil
  | consS :         @Crystal _ _ (n    ) (m    ) t₁   t₂ →
                    @Crystal _ _ (n + 1) (m + 1) (.cons h₁ t₁) (.cons h₁ t₂)
end ListFunctor

structure CoList (α : Type u) where
  f : Nat → Nat

  -- Technically this property is redutnant as cryst implies it
  -- Or it implies a more granular form at least
  -- cryst imples that it always increases except when it has grown to full size
  /- mono : ∀ n, f n < f n.succ -/

  obj : (n : Nat) → (f n).repeat (ListFunctor α) PUnit.{u + 1}
  cryst : ∀ n, ListFunctor.Crystal (obj n) (obj n.succ)

def ListFunctor.Crystal.mono
    {α : Type v} {b : Type (max u v)} {n m : Nat}
    {x : n.repeat (ListFunctor α) b}
    {y : m.repeat (ListFunctor α) b}
    (h : ListFunctor.Crystal.{u, v} x y)
    : n ≤ m :=
  match n, m with
  | 0, _+1   => Nat.le_add_left _ _
  | n+1, m+1 => by
    apply Nat.add_le_add_right _ 1
    cases h
    · assumption
    · exact mono (by assumption)

def CoList.mono
    {f : Nat → Nat}
    {obj : (n : Nat) → (f n).repeat (ListFunctor α) PUnit}
    (h : ∀ n, ListFunctor.Crystal (obj n) (obj n.succ))
    (n m : Nat)
    (hle : n ≤ m)
    : f n ≤ f m :=
  match hle with
  | .refl => .refl
  | .step (m := m) hle => calc
    f n ≤ f m := mono h _ _ hle
    _ ≤ _ := ListFunctor.Crystal.mono $ h _

def CoList.nil : CoList α where
  f     := fun _ => 1
  obj   := fun _ => .nil
  cryst := fun _ => .nilS $ Nat.zero_le 0

def CoList.cons (hd : α) : CoList α → CoList α
  | ⟨f, obj, cryst⟩ => {
    f     := Nat.succ ∘ f
    obj   := (.cons hd $ obj ·)
    cryst := λ _ => .consS $ cryst _
  }

def CoList.corec.impl
    (f : ρ → ListFunctor α ρ) (content : ρ)
    : {x : ℕ} → x.repeat (ListFunctor α) Unit
  | 0 => .unit
  | _+1 => match f content with
    | .nil => .nil
    | .cons hd tl => .cons hd (impl f tl)

def CoList.corec.proof : {n m : ℕ} → n < m →
    ListFunctor.Crystal (impl gen v (x := n)) (impl gen v (x := m))
  | 0, m+1, _ => .base
  | n+1, m+1, hlt => by
    dsimp [corec.impl]
    match gen v with
    | .nil      => exact .nilS $ Nat.le_of_lt $ Nat.succ_lt_succ_iff.mp hlt
    | .cons _ _ => exact .consS $ corec.proof $ Nat.succ_lt_succ_iff.mp hlt

def CoList.corec (f : ρ → ListFunctor α ρ) (content : ρ) : CoList α where
  f     := (2 ^ ·)
  obj   := fun _ => corec.impl f content
  cryst := (corec.proof $ Nat.pow_lt_pow_of_lt .refl $ Nat.lt_add_one ·)

def HEq.dependentRw
    {α : Sort _} {a b : α}
    {submotive : α → Sort _} {motive : (base : α) → submotive base → Sort _}
    {x : submotive a} {y : submotive b}
    (hParEq : a = b)
    (hEq : HEq x y)
    (src : motive a x)
    : motive b y := by
  subst hParEq
  subst hEq
  exact src

/- set_option pp.explicit true in -/
def CoList.dest (o : CoList α) : ListFunctor.{u} α (CoList α) :=
  let ⟨f, o, cryst⟩ := o
  match h₁ : f 0, hv₁ : o 0 with
  | n+1, v   => body f o cryst h₁ v hv₁
  | 0, .unit =>
    match h₂ : f 1, hv₂ : o 1 with
    | 0, .unit => False.elim $ by
      suffices z : @ListFunctor.Crystal.{u, u} α PUnit.{u + 1} 0 0 .unit .unit by
        cases z
      apply HEq.dependentRw
        (submotive := (Nat.repeat _ · _))
        (motive    := fun _ v => ListFunctor.Crystal (m := 0) v _)
        h₁ hv₁
      apply HEq.dependentRw
        (submotive := (Nat.repeat _ · _))
        (motive    := fun _ v => ListFunctor.Crystal _ v)
        h₂ hv₂
      exact cryst 0
    | n+1, v =>
      body (f ∘ Nat.succ) (fun x : Nat => o x.succ) (fun x : Nat => cryst x.succ) h₂ v hv₂
where
  body {n} f o cryst (h : f 0 = n + 1) v hv :=
    match hv : v with
    | .nil => .nil
    | .cons hd _ =>
      .cons hd ⟨
        (Nat.pred $ f ·),
        fun x =>
          have m := mono cryst 0 x (Nat.zero_le x)
          let this : Nat.repeat (ListFunctor α) (f x) PUnit.{u + 1} → Nat.repeat (ListFunctor α) (f x).pred _ :=
            match hm : f x with
            | 0 => False.elim
              $ Nat.not_succ_le_zero _ $ Eq.trans_le h.symm $ m.trans_eq hm
            | n+1 => fun x => match x with
              | .cons _ tl => tl
              | .nil =>
                sorry
          this $ o x,
        sorry
      ⟩
  /-
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
    -/
