import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic
import LeanScratch.HEq

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

def Crystal.trans
    {base : Type _}
    : {n m k : Nat} →
    {a : n.repeat (ListFunctor.{v, max u v} α) base} →
    {b : m.repeat (ListFunctor.{v, max u v} α) base} →
    {c : k.repeat (ListFunctor.{v, max u v} α) base} →
    Crystal a b → Crystal b c → Crystal a c
  | _+1, _+1, _+1, .cons _ _, .cons _ _, .cons _ _, .consS hx, .consS hy =>
    .consS $ Crystal.trans hx hy
  | _+1, _+1, _+1, _, _, _, .nilS hx, .nilS hy =>
    .nilS $ Nat.le_trans hx hy
  | 0, _+1, _+1, _, _, _, .base, _ => .base

def Crystal.zero_up
    {α : Type _}
    {f : Nat → Nat}
    {obj : (n : Nat) → (f n).repeat (ListFunctor α) PUnit}
    (cryst : ∀ (n : Nat), ListFunctor.Crystal (obj n) (obj n.succ))
    : (n : Nat) → Crystal (obj 0) (obj n.succ)
  | n+1 => Crystal.zero_up cryst n |>.trans $ cryst _
  | 0   => cryst 0

def Crystal.frwd
    {α : Type _}
    {f : Nat → Nat}
    {obj : (n : Nat) → (f n).repeat (ListFunctor α) PUnit}
    (cryst : ∀ (n : Nat), ListFunctor.Crystal (obj n) (obj n.succ))
    : (a b : Nat) → a < b → Crystal (obj a) (obj b)
  | a+1, b+1, h => frwd
    (f := f ∘ Nat.succ)
    (obj := (obj ·.succ))
    (cryst ·.succ) a b
    (Nat.succ_lt_succ_iff.mp h)
  | 0,   _+1, _ => zero_up cryst _
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

def CoList.dest.ex1
    {α : Type u} {n : ℕ}
    {f : ℕ → ℕ}
    {x : ℕ}
    {o : (x : ℕ) → Nat.repeat (ListFunctor α) (f x) PUnit.{u + 1}}
    {hd : α}
    {tl : Nat.repeat (ListFunctor α) n PUnit.{u + 1}}

    (h : f 0 = n + 1)

    (hv : HEq (o 0) (ListFunctor.cons hd tl))
    (this : ListFunctor.Crystal (o 0) (o (x + 1)))
    : Nat.repeat (ListFunctor α) (f x.succ).pred PUnit.{u + 1} :=
  match hCarryF : f 0, f (x + 1), hCarryO : o 0, o (x + 1), this with
  | _+1, _+1, .cons _ _, .cons _ t, _ => t

  | 0, _+1, _, _, _
  | 0, 0,   _, _, _ =>
    Nat.noConfusion $ h.symm.trans hCarryF

  | _+1, _+1, .nil, _, _
  | _+1, 0,   .nil, _, _ => False.elim $ by
    obtain rfl := Nat.succ.inj $ h.symm.trans hCarryF
    exact ListFunctor.noConfusion $ eq_of_heq $ hCarryO.symm.trans hv

  | _, 0, _, _, h 
  | _+1, _+1, .cons _ _, .nil, h => False.elim $ by cases h

def CoList.dest.ex
    {α : Type u} {n : ℕ}
    {f : ℕ → ℕ}
    {o : (x : ℕ) → Nat.repeat (ListFunctor α) (f x) PUnit.{u + 1}}

    (cryst : ∀ (n : ℕ), ListFunctor.Crystal (o n) (o n.succ))
    (h : f 0 = n + 1)

    (hd : α)
    (tl : Nat.repeat (ListFunctor α) n PUnit.{u + 1})

    (hv : HEq (o 0) (ListFunctor.cons hd tl))
    (x : ℕ)
    : Nat.repeat (ListFunctor α) (f x).pred PUnit.{u + 1} :=
  match x with
  | 0   => cast (by rw [h, Nat.pred_succ]) tl
  | x+1 =>
    have := ListFunctor.Crystal.frwd cryst 0 (x+1) (Nat.zero_lt_succ x)
    ex1 h hv this

def CoList.dest.body {α : Type u} {n : ℕ}
    (f : ℕ → ℕ) (o : (x : ℕ) → Nat.repeat (ListFunctor α) (f x) PUnit)

    (cryst : ∀ (n : ℕ), ListFunctor.Crystal (o n) (o n.succ))
    (h : f 0 = n + 1)
    (v : Nat.repeat (ListFunctor α) (n + 1) PUnit.{u + 1})
    (hv : HEq (o 0) v)
    : ListFunctor α (CoList α) :=
  match v with
  | .nil => .nil
  | .cons hd tl =>
    .cons hd ⟨
      (Nat.pred $ f ·),
      dest.ex cryst h hd tl hv,
      fun
        | n+1 => by
          dsimp
          sorry
        | 0 => by
          dsimp [ex, ex1]
          sorry
      /- fun -/
      /- | 0 => by -/
      /-   dsimp -/
      /-   sorry -/
      /-   /- split -/ -/
      /-   /- sorry -/ -/
      /- | x+1 => by -/
      /-   /- have := ListFunctor.Crystal.frwd cryst 0 (x+1) (Nat.zero_lt_succ x) -/ -/
      /-   dsimp -/
      /-   sorry -/
        /- sorry -/
        /- match hCarryF : f 0, f (x + 1), hCarryO : o 0, o (x + 1), this with -/
        /- | _, _, _, _, _ => sorry -/
        /- | _+1, _+1, .cons _ _, .cons _ t, _ => sorry -/
        /- | 0, _+1, _, _, _ -/
        /- | 0, 0, _, _, _ => sorry -/
        /- | _+1, _+1, .nil, _, _ -/
        /- | _+1, 0, .nil, _, _ => sorry -/
    ⟩



/- set_option pp.explicit true in -/
def CoList.dest (o : CoList α) : ListFunctor.{u} α (CoList α) :=
  let ⟨f, o, cryst⟩ := o
  match h₁ : f 0, hv₁ : o 0 with
  | n+1, v   => dest.body f o cryst h₁ v hv₁
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
      dest.body (f ∘ Nat.succ) (fun x : Nat => o x.succ) (fun x : Nat => cryst x.succ) h₂ v hv₂

