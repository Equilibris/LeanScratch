import LeanScratch.Semantics.STLC.Stx

namespace STLC

-- TODO: look into Coc to try to understand how this nonsense works
-- It would be really neat if I could use a type function as a argument type in a mutual manor here

def Arity : Ty → ℕ
  | .direct _ => 0
  | .arr _ b => (Arity b) + 1

def ArgCount : Ty → Type
  | .arr a b  => ArgCount a → ArgCount b
  | .direct _ => ℕ

namespace ArgCount

mutual
def lt (a b : ArgCount z) : Prop := match z with
  | .direct _ => Nat.lt a b
  | .arr _ _ => ∀ x, Monotonic x → lt (a x) (b x)

-- Not really a LE as it doest satisfy le ↔ lt ∧ neq
def le (a b : ArgCount z) : Prop := match z with
  | .direct _ => Nat.le a b
  | .arr _ _ => ∀ x, Monotonic x → le (a x) (b x)

def Monotonic (v : ArgCount s) : Prop := match s with
  | .direct _ => True
  | .arr argTy _ =>
    -- Might need to add the restrictions Monotonic a and Monotonic b
    (∀ a b : ArgCount argTy, Monotonic a → Monotonic b →  le a b → le (v a) (v b)) ∧
      (∀ x : ArgCount argTy, Monotonic x → Monotonic (v x))
end

instance : LT (ArgCount z) := ⟨lt⟩
instance : LE (ArgCount z) := ⟨le⟩

def inc (h : ArgCount v) : ArgCount v := match v with
  | .direct _ => Nat.succ h
  | .arr _ _ => fun a' => inc (h a')

def addN (h : ArgCount v) (n : ℕ) : ArgCount v := match v with
  | .direct _ => Nat.add h n
  | .arr _ _ => fun a' => addN (h a') n

instance : HAdd (ArgCount v) ℕ (ArgCount v) := ⟨addN⟩
theorem add_def {a : ArgCount v} {n : ℕ} : a + n = addN a n := rfl

theorem addN_succ_inc {v : ArgCount t} : addN v (n + 1) = inc (addN v n) :=
  match t with
  | .direct _ => rfl
  | .arr a b => by
    dsimp [addN, inc]
    apply funext
    intro v
    rw [addN_succ_inc]

theorem addN_zero {v : ArgCount t} : addN v 0 = v :=
  match t with
  | .direct _ => rfl
  | .arr _ _ => by
    dsimp [addN, inc]
    apply funext
    intro x
    rw [addN_zero]

def zero : ArgCount v := match v with
  | .direct _ => Nat.zero
  | .arr _ _ => fun _ => ArgCount.zero
def naturalize (h : ArgCount v) : ℕ := match v with
  | .direct _ => h
  | .arr _ _ => naturalize (h ArgCount.zero)

@[simp]
theorem naturalize_zero : naturalize (@zero v) = 0 := match v with
  | .direct _ => rfl
  | .arr _ _ => by dsimp [naturalize]; exact naturalize_zero

@[simp]
theorem naturalize_inc
    (x : ArgCount z)
    : naturalize (inc x) = (naturalize x) + 1 :=
  match z with
  | .direct _ => rfl
  | .arr _ _ => by dsimp [naturalize, inc]; rw [naturalize_inc]

@[simp]
theorem naturalize_addN {a : ArgCount ty} : (addN a n).naturalize = a.naturalize + n :=
  match ty with
  | .direct _ => rfl
  | .arr a b => by
    dsimp [addN, naturalize]
    exact naturalize_addN

theorem lt_trans {a b c : ArgCount t} (hab : a < b) (hbc : b < c) : a < c :=
  match t with
  | .direct _ => by
    change lt _ _ at hab hbc ⊢
    simp only [lt] at hab hbc ⊢
    exact Nat.lt_trans hab hbc
  | .arr _ _ => by
    change lt _ _ at hab hbc ⊢
    simp only [lt] at hab hbc ⊢
    intro x xm
    exact lt_trans (hab x xm) (hbc x xm)

theorem le_trans {a b c : ArgCount t} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  match t with
  | .direct _ => by
    change le _ _ at hab hbc ⊢
    simp only [le] at hab hbc ⊢
    exact Nat.le_trans hab hbc
  | .arr _ _ => by
    change le _ _ at hab hbc ⊢
    simp only [le] at hab hbc ⊢
    intro x xm
    specialize hab x xm
    specialize hbc x xm
    exact le_trans hab hbc

theorem le_of_lt {a b : ArgCount z} : a < b → a ≤ b :=
  match z with
  | .direct _ => fun h => by
    change lt _ _ at h
    change le _ _
    simp only [lt, Nat.lt_eq, le, Nat.le_eq] at h ⊢
    exact Nat.le_of_succ_le h
  | .arr _ _ => by
    change lt _ _ → le _ _
    simp only [lt, le]
    exact fun h x xm => le_of_lt (h x xm)

theorem self_le_self {a : ArgCount z} : a ≤ a :=
  match z with
  | .direct _ => by
    change le _ _
    simp only [le, Nat.le_eq, le_refl]
  | .arr _ _ => by
    change le _ _
    simp only [le]
    intro x _
    exact self_le_self

theorem zero_Monotonic : Monotonic (@zero s) := match s with
  | .direct _ => by simp only [Monotonic]
  | .arr _ _ => by
    simp only [Monotonic, zero]
    exact ⟨fun _ _ _ _ _ => self_le_self, fun _ _ => zero_Monotonic⟩

theorem le_congr
    {aF bF : ArgCount (.arr f r)}
    {aR bR : ArgCount f}
    (hAFMono : Monotonic aF)
    (hARMono : Monotonic aR)
    (hBRMono : Monotonic bR)
    (hFLe : aF ≤ bF)
    (hRLe : aR ≤ bR)
    : aF aR ≤ bF bR := by
  change le _ _ at hFLe hRLe ⊢
  simp only [le] at hFLe hRLe
  simp only [Monotonic] at hAFMono hARMono
  exact le_trans (hAFMono.1 aR bR hARMono hBRMono hRLe) (hFLe bR hBRMono)

/- def strongNeq (a b : ArgCount z) : Prop := match z with -/
/-   | .direct _ => a ≠ b -/
/-   | .arr _ _ => ∀ x, strongNeq (a x) (b x) -/

/- theorem le_strongNeq_lt {a b : ArgCount z} (hLe : a ≤ b) (hNeq : strongNeq a b) : a < b := -/
/-   match z with -/
/-   | .direct _ => Nat.lt_iff_le_and_ne.mpr ⟨hLe, hNeq⟩ -/
/-   | .arr _ _ => fun x => le_strongNeq_lt (hLe x) (hNeq x) -/

/- theorem le_lt {a b : ArgCount z} (hLe : a ≤ b) (hNeq : a ≠ b) : a < b := -/
/-   match z with -/
/-   | .direct _ => Nat.lt_iff_le_and_ne.mpr ⟨hLe, hNeq⟩ -/
/-   | .arr _ _ => by -/
/-     sorry -/

/- theorem le_iff_lt_or_eq {a b : ArgCount z} : a ≤ b ↔ (a < b ∨ a = b) := -/
/-   match z with -/
/-   | .direct _ => Nat.le_iff_lt_or_eq -/
/-   | .arr fn arg => by -/
/-     /- change (∀ x, _) ↔ _ -/ -/
/-     /- apply forall_congr' -/ -/
/-     constructor -/
/-     · intro h -/
/-       by_cases this : a = b -/
/-       · exact .inr this -/
/-       · sorry -/
/-       /- apply forall_or_right.mp -/ -/
/-       /- apply forall_congr' -/ -/
/-       /- intro x -/ -/
/-       /- rcases le_iff_lt_or_eq.mp (h x) with (h|h') -/ -/
/-       /- · exact .inl h -/ -/
/-       /- · right -/ -/
/-       /-   induction arg -/ -/
/-       /-   · sorry -/ -/
/-       /-   · sorry -/ -/
/-       /- exact fun h => le_iff_lt_or_eq.mp h -/ -/
/-     · rintro (h|rfl) -/
/-       · exact le_of_lt h -/
/-       · exact self_le_self -/

/- theorem le_forward {a b : ArgCount (.arr a' b')} () : a ≤ b := sorry -/

theorem lt_naturalize {a b : ArgCount v} (h : a < b) : naturalize a < naturalize b :=
  match v with
  | .direct _ => by
    change lt _ _ at h
    simp only [lt, naturalize] at h ⊢
    exact h
    /- h -/
  | .arr _ _ => by
    change lt _ _ at h
    simp only [ArgCount, lt, naturalize] at a b h ⊢
    exact lt_naturalize $ h zero zero_Monotonic

theorem le_naturalize {a b : ArgCount v} (h : a ≤ b) : naturalize a ≤ naturalize b :=
  match v with
  | .direct _ => by
    change le _ _ at h
    simp only [le, naturalize] at h ⊢
    exact h
    /- h -/
  | .arr _ _ => by
    change le _ _ at h
    simp only [ArgCount, le, naturalize] at a b h ⊢
    exact le_naturalize $ h zero zero_Monotonic

@[simp]
theorem self_lt_addN {a : ArgCount t} (h : 0 < n) : a < addN a n :=
  match t with
  | .direct _ => by
    change lt _ _
    simp only [ArgCount, addN, le] at a ⊢
    exact Nat.lt_add_of_pos_right h
  | .arr _ _ => by
    change lt _ _
    simp only [ArgCount, addN, le] at a ⊢
    exact fun _ _ => self_lt_addN h

@[simp]
theorem addN_lt_addN_right {a b : ArgCount t} (h : a < b) : addN a n < addN b n := match t with
  | .direct _ => by
    change lt _ _ at h
    change lt _ _
    simp only [ArgCount, addN, lt] at a b h ⊢
    exact Nat.add_lt_add_right h _
  | .arr _ _ => by
    change lt _ _ at h
    change lt _ _
    simp only [ArgCount, addN, lt] at a b h ⊢
    exact fun z zMono => addN_lt_addN_right (h z zMono)

@[simp]
theorem addN_lt_addN_left {n : ArgCount t} (h : a < b) : addN n a < addN n b := match t with
  | .direct _ => by 
    change lt _ _
    simp only [ArgCount, addN, lt] at a b h ⊢
    exact Nat.add_lt_add_left h n
  | .arr _ _ => by
    change lt _ _
    simp only [ArgCount, addN, lt] at a b h ⊢
    exact fun _ _ => addN_lt_addN_left h

/- @[simp] -/
/- theorem addN_le_addN_right {a b : ArgCount t} (h : (a < b) ∨ a = b) : (addN a n < addN b n) ∨ addN a n = addN b n := match h with -/
/-   | .inl h => .inl (addN_lt_addN_right h) -/
/-   | .inr rfl => .inr rfl -/

/- @[simp] -/
/- theorem addN_le_addN_left {n : ArgCount t} (h : (a < b) ∨ a = b) : addN n a < addN n b ∨ addN n a = addN n b := -/
/-   match h with -/
/-   | .inl h => .inl (addN_lt_addN_left h) -/
/-   | .inr rfl => .inr rfl -/

@[simp]
theorem addN_le_addN_right {a b : ArgCount t} (h : (a ≤ b)) : (addN a n ≤ addN b n) := 
  match t with
  | .direct _ => by
    change le _ _ at h
    change le _ _
    simp only [addN, lt, le] at a b h ⊢
    exact Nat.add_le_add_right h n
  | .arr _ _ => by
    change le _ _ at h
    change le _ _
    simp only [addN, lt, le] at a b h ⊢
    exact fun x xm => addN_le_addN_right (h x xm)

@[simp]
theorem addN_le_addN_left {n : ArgCount t} (h : (a ≤ b)) : addN n a ≤ addN n b :=
  match t with
  | .direct _ => by
    change le _ _
    simp only [addN, lt, le] at a b h ⊢
    exact Nat.add_le_add_left h n
  | .arr _ _ => by
    change le _ _
    simp only [addN, lt, le] at a b h ⊢
    exact fun _ _ => addN_le_addN_left h

-- I wish this could be an inductive but its too complex
def addN_Monotonic {v : ArgCount s} (h : Monotonic v)
    : Monotonic (addN v n) := match s with
  | .direct _ => by
    simp only [addN, Monotonic] at h v ⊢
  | .arr _ _ => by
    simp only [addN, Monotonic] at h v ⊢
    exact ⟨fun a b aMono bMono hLt => addN_le_addN_right (h.1 a b aMono bMono hLt), (addN_Monotonic $ h.right · ·)⟩

theorem le_addN_lt_lt {a b : ArgCount t} (hLe : a ≤ b) (hLt : n < m) : a.addN n < b.addN m :=
  match t with
  | .direct _ => by
    change le _ _ at hLe
    change lt _ _
    simp only [addN, lt, le] at hLe ⊢
    exact (Nat.add_le_add_right hLe n).trans_lt (Nat.add_lt_add_left hLt b)
  | .arr _ _ => by
    change le _ _ at hLe
    change lt _ _
    simp only [addN, lt, le] at hLe ⊢
    exact fun x xm => le_addN_lt_lt (hLe x xm) hLt

theorem lt_sufficency
    {a b : ArgCount (.arr f t)} {c : ArgCount f}
    (cMono : Monotonic c)
    (h : a < b) : a c < b c := by
  change lt _ _ at h ⊢
  simp only [lt] at *
  exact h c cMono

theorem le_trans_lt
    {a b c : ArgCount t}
    (h1 : a ≤ b)
    (h2 : b < c)
    : a < c :=
  match t with
  | .direct _ => by
    change le _ _ at h1
    change lt _ _ at h2 ⊢
    simp only [le, lt, ArgCount] at a b c h1 h2 ⊢
    exact Nat.lt_of_le_of_lt h1 h2
  | .arr _ _ => by
    change le _ _ at h1
    change lt _ _ at h2 ⊢
    simp only [le, lt, ArgCount] at a b c h1 h2 ⊢
    intro x xm
    exact le_trans_lt (h1 x xm) (h2 x xm)

end ArgCount

