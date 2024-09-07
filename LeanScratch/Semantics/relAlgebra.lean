abbrev dyn := (t : Type _) × t
abbrev Rel key fieldDesc := key → fieldDesc → dyn → Prop

inductive RA : Type → Type → Type _ :=
  | base (r : Rel key fd) : RA key fd

  | select (pred : fd → dyn → Prop) (deep : RA key fd) : RA key fd
  | rename (rn   : fd → fd)         (deep : RA key fd) : RA key fd
  | proj   (p    : key → Prop)      (deep : RA key fd) : RA key fd

  | prod (a : RA α fdα) (b : RA β fdβ) : RA (α × β) (fdα ⊕ fdβ)

  | diff  (a b : RA α fd) : RA α fd
  | union (a b : RA α fd) : RA α fd
  | inter (a b : RA α fd) : RA α fd

abbrev σ : (fd → dyn → Prop) → RA key fd → RA key fd := RA.select
abbrev π : (key → Prop) → RA key fd → RA key fd := RA.proj
abbrev ρ : (fd → fd) → RA key fd → RA key fd := RA.rename

def RA.denote : RA key fd → Rel key fd
  | .base r => r
  | .select pred deep => fun key fd v => deep.denote key fd v ∧ pred fd v
  | .proj   pred deep => fun key fd v => deep.denote key fd v ∧ pred key
  | .prod a b => fun
    | k, .inl x => a.denote k.1 x
    | k, .inr x => b.denote k.2 x
  | .diff  a b => fun key fd v => a.denote key fd v ∧ ¬∃ v, b.denote key fd v
  | .union a b => fun key fd v => a.denote key fd v ∨       b.denote key fd v
  | .inter a b => fun key fd v => a.denote key fd v ∧       b.denote key fd v
  | .rename rn deep => (deep.denote · ∘ rn)

abbrev RA.ERel (a b : RA key fd) := a.denote = b.denote

infixr:50 " ≃ " => RA.ERel

theorem RA.ERel.refl : a ≃ a := rfl
theorem RA.ERel.symm : b ≃ a → a ≃ b := Eq.symm
theorem RA.ERel.trans : a ≃ b → b ≃ c → a ≃ c := Eq.trans

theorem σ_comm : σ f (σ g R) ≃ σ g (σ f R) := by
  ext key y v
  simp [RA.denote]
  exact and_right_comm
theorem π_comm : π f (π g R) ≃ π g (π f R) := by
  ext key y v
  simp [RA.denote]
  exact and_right_comm

@[simp]
theorem σ_compress : σ f (σ g R) ≃ σ (fun x v => f x v ∧ g x v) R := by
  ext key y v
  dsimp [RA.denote]
  rw [and_assoc, @and_comm (g _ _)]
@[simp]
theorem π_compress : π f (π g R) ≃ π (fun x => f x ∧ g x) R := by
  ext key y v
  dsimp [RA.denote]
  rw [and_assoc, @and_comm (g _)]
