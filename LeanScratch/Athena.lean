def listF (α : Type _) : Nat → Type
  | 0 => Unit
  | n+1 => α × listF α n

def list (α : Type _) : Type := (n : Nat) × listF α n

/- def bbtF (α : Type _) : Nat → Type -/
/-   | 0 => Unit -/
/-   | n+1 => α × bbtF α n × bbtF α n -/

-- a + b = Σ_n ∈ Bool

/- def sumx (α β : Type _) : Type _ := -/
/-   (b : Bool) × (match b with | .true => α | .false => β) -/

/- def v : sumx Nat Bool := ⟨.false, Bool.true⟩ -/

inductive list' (α : Type _)
  | nil
  | cons (hd : α) (tl : list' α)

inductive Len : List α → Nat → Prop
  | nil : Len [] 0
  | cons : Len t n → Len (hd :: t) n.succ

example (h : Len tl n) : Len ([a, b, c] ++ tl) (n + 3) := by
  sorry

-- ListFunctor α Empty
-- ListFunctor α (ListFunctor α Empty)

inductive Bag : List Nat → Type
  | leaf : Bag []
  | introduce (idx : Nat) (bag : Bag sub) : Bag (idx :: sub)
  | forget    (idx : Nat) (bag : Bag sub) : Bag (sub.removeAll [idx])

def SomeBag := PSigma Bag



def Eq' {A : Type} (a b : A) : Prop :=
  ∀ (P : A → Prop), P a → P b

example {A : Type} {a b : A} : a = b ↔ Eq' a b := ⟨ (·.rec λ _ ↦ id), (· (a = ·) rfl) ⟩

inductive Action : Type 1
  | handle : (a : Type 0) → (a → Action) → Action

def list : (n : Nat) × n.repeat (· × A) Unit

