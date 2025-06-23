inductive ITreeF (E : Type u → Type u) (R : Type u) (ρ : Type (u+1)) : Type (u+1)
  | ret (v : R)
  | tau (t : ρ)
  | vis {A : Type u} (e : E A) (cont : A → ρ)

namespace ITree
inductive Crystal {base : Type (u+1)} :
    {n : Nat} →
    {m : Nat} →
    n.repeat (ITreeF.{u} E R) base →
    m.repeat (ITreeF.{u} E R) base → Prop where
  | base :         Crystal (n := 0    ) (m := m + 1) b v
  | retS : n ≤ m → Crystal (n := n + 1) (m := m + 1) (.ret _) (.ret _)
  | tauS :         Crystal (n := n    ) (m := m    ) t₁   t₂ →
                   Crystal (n := n + 1) (m := m + 1) (.tau t₁) (.tau t₂)
  | visS :   (∀ x, Crystal (n := n    ) (m := m    ) (f₁ x)   (f₂ x)) →
                   Crystal (n := n + 1) (m := m + 1) (.vis e f₁) (.vis e f₂)

def Crystal.trans
    {base : Type _}
    : {n m k : Nat} →
    {a : n.repeat (ITreeF E R) base} →
    {b : m.repeat (ITreeF E R) base} →
    {c : k.repeat (ITreeF E R) base} →
    Crystal a b → Crystal b c → Crystal a c
  | _+1, _+1, _+1, _, _, _, .tauS hx, .tauS hy =>
    .tauS $ Crystal.trans hx hy
  | _+1, _+1, _+1, _, _, _, .visS hx, .visS hy =>
    .visS $ fun z => Crystal.trans (hx z) (hy z)
  | _+1, _+1, _+1, _, _, _, .retS hx, .retS hy =>
    .retS $ Nat.le_trans hx hy
  | 0, _+1, _+1, _, _, _, .base, _ => .base

def Crystal.zero_up
    {f : Nat → Nat}
    {obj : (n : Nat) → (f n).repeat (ITreeF E R) PUnit}
    (cryst : ∀ (n : Nat), Crystal (obj n) (obj n.succ))
    : (n : Nat) → Crystal (obj 0) (obj n.succ)
  | n+1 => Crystal.zero_up cryst n |>.trans $ cryst _
  | 0   => cryst 0

def Crystal.frwd
    {f : Nat → Nat}
    {obj : (n : Nat) → (f n).repeat (ITreeF E R) PUnit}
    (cryst : ∀ (n : Nat), Crystal (obj n) (obj n.succ))
    : (a b : Nat) → a < b → Crystal (obj a) (obj b)
  | a+1, b+1, h => Crystal.frwd
    (f := f ∘ Nat.succ)
    (obj := (obj ·.succ))
    (cryst ·.succ) a b
    (Nat.succ_lt_succ_iff.mp h)
  | 0,   _+1, _ => Crystal.zero_up cryst _

def Crystal.tau
    {n m : Nat}
    {x}
    {obj : (n : Nat) → n.repeat (ITreeF E R) PUnit}
    (v : Crystal (obj n.succ) (obj m.succ))
    (h : obj n.succ = .tau x)
    : ∃ x, obj m.succ = .tau x := by
  cases h2 : obj m.succ <;> rw [h2, h] at v <;> cases v
  exact ⟨_, rfl⟩
def Crystal.vis
    {n m : Nat} {x}
    {obj : (n : Nat) → n.repeat (ITreeF E R) PUnit}
    (v : Crystal (obj n.succ) (obj m.succ))
    (h : obj n.succ = .vis e x)
    : ∃ x, obj m.succ = .vis e x := by
  cases h2 : obj m.succ <;> rw [h2, h] at v <;> cases v
  exact ⟨_, rfl⟩

end ITree

structure ITree (E : Type u → Type u) (R : Type u) : Type (u+1) where
  obj : (n : Nat) → n.repeat (ITreeF E R) PUnit
  cryst : ∀ n, ITree.Crystal (obj n) (obj n.succ)

namespace ITree

def ret (v : R) : ITree E R := ⟨
  fun | 0 => .unit | _+1 => .ret v,
  fun | 0 => .base | n+1 => .retS (Nat.le_add_right n 1)
⟩

def tau (x : ITree E R) : ITree E R := ⟨
  fun | 0 => .unit | n+1 => .tau (x.obj n),
  fun | 0 => .base | n+1 => .tauS (x.cryst n)
⟩

def vis (e : E A) (cont : A → ITree E R) : ITree E R := ⟨
  fun | 0 => .unit | n+1 => .vis e fun x => (cont x).obj   n,
  fun | 0 => .base | n+1 => .visS  fun x => (cont x).cryst n
⟩

def corec.impl
    (f : ρ → ITreeF E R ρ) (content : ρ)
    : (x : Nat) → x.repeat (ITreeF E R) PUnit
  | 0 => .unit
  | _+1 => match f content with
    | .ret x => .ret x
    | .tau x => .tau (impl f x _)
    | .vis e x => .vis e (fun v => impl f (x v) _)

def corec.proof : ∀ (x : Nat), Crystal (impl f v x) (impl f v x.succ)
  | 0 => .base
  | n+1 => by
    dsimp [corec.impl]
    exact match f v with
    | .ret r   => .retS $ Nat.le_add_right n 1
    | .tau v   => .tauS $ proof n
    | .vis e m => .visS λx ↦ proof n

def corec (f : ρ → ITreeF E R ρ) (v : ρ) : ITree E R :=
  ⟨corec.impl f v, corec.proof⟩

def dest (o : ITree E R) : ITreeF E R (ITree E R) :=
  let ⟨obj, cryst⟩ := o
  match h₁ : obj 1 with
  | .ret x   => .ret x
  | .tau x   => .tau ⟨
      fun x => match h₂ : obj x.succ with
      | .tau x => x
      | .vis _ _ | .ret _ =>
        -- We need False.elim to make the univ were eliming into be Prop
        False.elim (match x with
          | 0 => ITreeF.noConfusion $ h₁.symm.trans h₂
          | x+1 =>
            have := Crystal.frwd cryst 1 x.succ.succ (Nat.lt_of_sub_eq_succ rfl)
            match h₁' : (obj 1), h₂' : obj x.succ.succ, this with
            | _, _, .tauS v => ITreeF.noConfusion $ h₂'.symm.trans h₂
            | _, _, .visS v
            | _, _, .retS v => ITreeF.noConfusion $ h₁'.symm.trans h₁
            ) ,
      fun
        | 0 => .base
        | n+1 => by
          have h2 := Crystal.frwd cryst 1 (n + 2) (Nat.lt_of_sub_eq_succ rfl)
          have h3 := Crystal.frwd cryst 1 (n + 3) (Nat.lt_of_sub_eq_succ rfl)
          have hz := Crystal.frwd cryst (n + 2) (n + 3) (Nat.lt_add_one (n + 2))
          rw [h₁] at h2 h3
          dsimp
          split <;> rename_i heq <;> rw [heq] at h2 hz <;> cases h2
          split <;> rename_i heq <;> rw [heq] at h3 hz <;> cases h3
          cases hz
          rename_i hz
          exact hz
    ⟩
  | .vis e₁ x => .vis e₁ fun v => ⟨
      fun x => match h₂ : obj x.succ with
      | .vis e₂ f =>
        f (cast (by
          cases x
          · have ⟨x, _⟩ := (ITreeF.vis.injEq _ _ _ _ _).mp $ h₁.symm.trans h₂
            exact x
          next x =>
            have ⟨_, p⟩ := Crystal.vis
              (Crystal.frwd cryst 1 (x.succ.succ) (Nat.lt_of_sub_eq_succ rfl)) h₁
            have ⟨x, _⟩ := (ITreeF.vis.injEq _ _ _ _ _).mp $ p.symm.trans h₂
            exact x
          ) v)
      | .tau _ | .ret _ =>
        -- We need False.elim to make the univ were eliming into be Prop
        False.elim (match x with
          | 0 => ITreeF.noConfusion $ h₁.symm.trans h₂
          | x+1 =>
            have := Crystal.frwd cryst 1 x.succ.succ (Nat.lt_of_sub_eq_succ rfl)
            match h₁' : (obj 1), h₂' : obj x.succ.succ, this with
            | _, _, .visS v => ITreeF.noConfusion $ h₂'.symm.trans h₂
            | _, _, .tauS v
            | _, _, .retS v => ITreeF.noConfusion $ h₁'.symm.trans h₁
            ) ,
      fun
        | 0 => .base
        | n+1 => by
          have h2 := Crystal.frwd cryst 1 (n + 2) (Nat.lt_of_sub_eq_succ rfl)
          have h3 := Crystal.frwd cryst 1 (n + 3) (Nat.lt_of_sub_eq_succ rfl)
          have hz := Crystal.frwd cryst (n + 2) (n + 3) (Nat.lt_add_one (n + 2))
          rw [h₁] at h2 h3
          dsimp
          split <;> rename_i heq <;> rw [heq] at h2 hz <;> cases h2
          split <;> rename_i heq <;> rw [heq] at h3 hz <;> cases h3
          cases hz
          rename_i hz
          exact hz _
    ⟩

end ITree

