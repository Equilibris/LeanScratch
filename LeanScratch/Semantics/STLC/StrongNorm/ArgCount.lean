import LeanScratch.Semantics.STLC.Stx

namespace STLC

-- It would be really neat if I could use a type function as a argument type in a mutual manor here

def ArgCount : Ty → Type
  | .arr a b  => ArgCount a → ArgCount b
  | .direct _ => ℕ

def ArgCount.lt (a b : ArgCount z) : Prop := match z with
  | .direct _ => Nat.lt a b
  | .arr _ _ => ∀ x, lt (a x) (b x)

-- Not really a LE as it doest satisfy le ↔ lt ∧ neq
def ArgCount.le (a b : ArgCount z) : Prop := match z with
  | .direct _ => Nat.le a b
  | .arr _ _ => ∀ x, le (a x) (b x)

instance : LT (ArgCount z) := ⟨ArgCount.lt⟩
instance : LE (ArgCount z) := ⟨ArgCount.le⟩

def ArgCount.Monotonic (v : ArgCount s) : Prop := match s with
  | .direct _ => True
  | .arr argTy _ =>
    (∀ a b : ArgCount argTy, a < b → (v a ≤ v b) ) ∧
      (∀ x : ArgCount argTy, Monotonic (v x))

structure AC (t : Ty) : Type where
  data  : ArgCount t
  proof : ArgCount.Monotonic data

namespace ArgCount

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

theorem le_of_lt {a b : ArgCount z} : a < b → a ≤ b :=
  match z with
  | .direct _ => fun h => Nat.le_of_succ_le h
  | .arr _ _ => fun h x => le_of_lt (h x)

theorem self_le_self {a : ArgCount z} : a ≤ a :=
  match z with
  | .direct _ => Nat.le.refl
  | .arr _ _ => fun _ => self_le_self


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
  | .direct _ => h
  | .arr _ _ => by
    dsimp [naturalize]
    exact lt_naturalize $ h zero

@[simp]
theorem self_lt_addN {a : ArgCount t} (h : 0 < n) : a < addN a n :=
  match t with
  | .direct _ => Nat.lt_add_of_pos_right h
  | .arr _ _ => fun _ => self_lt_addN h

@[simp]
theorem addN_lt_addN_right {a b : ArgCount t} (h : a < b) : addN a n < addN b n := match t with
  | .direct _ => Nat.add_lt_add_right h _
  | .arr _ _ => fun z => addN_lt_addN_right (h z)

@[simp]
theorem addN_lt_addN_left {n : ArgCount t} (h : a < b) : addN n a < addN n b := match t with
  | .direct _ => Nat.add_lt_add_left h n
  | .arr _ _ => fun _ => addN_lt_addN_left h

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
  | .direct _ => Nat.add_le_add_right h n
  | .arr _ _ => fun x => addN_le_addN_right (h x)

@[simp]
theorem addN_le_addN_left {n : ArgCount t} (h : (a ≤ b)) : addN n a ≤ addN n b :=
  match t with
  | .direct _ => Nat.add_le_add_left h n
  | .arr _ _ => fun _ => addN_le_addN_left h

-- I wish this could be an inductive but its too complex
def addN_Monotonic {v : ArgCount s} (h : Monotonic v)
    : Monotonic (addN v n) := match s with
  | .direct _ => True.intro
  | .arr _ _ => 
    ⟨fun a b hLt => addN_le_addN_right (h.1 a b hLt), (addN_Monotonic $ h.right ·)⟩

theorem zero_Monotonic : Monotonic (@zero s) := match s with
  | .direct _ => True.intro
  | .arr _ _ => ⟨fun _ _ _ => self_le_self, fun _ => zero_Monotonic⟩

theorem le_addN_lt_lt {a b : ArgCount t} (hLe : a ≤ b) (hLt : n < m) : a.addN n < b.addN m :=
  match t with
  | .direct _ => (Nat.add_le_add_right hLe n).trans_lt (Nat.add_lt_add_left hLt b)
  | .arr _ _ => fun x => le_addN_lt_lt (hLe x) hLt

end ArgCount

