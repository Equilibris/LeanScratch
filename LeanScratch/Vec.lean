import LeanScratch.Fin2

inductive Vec (T : Type u) : Nat → Type u
  | nil : Vec T 0
  | cons (hd : T) (tl : Vec T n) : Vec T n.succ
deriving DecidableEq

instance : Inhabited (Vec T 0) where
  default := .nil

instance : Unique (Vec T 0) where uniq | .nil => rfl

infixr:20 " %:: " => Vec.cons
notation:20 "%[]" => Vec.nil

instance [Repr T] : Repr (Vec T n) where
  reprPrec ls prec := .bracket "%[" (tail prec ls) "]"
    where
      tail {z} prec : Vec _ z → _
        | %[] => .nil
        | hd %:: tl@(.nil) => .append (reprPrec hd prec) $ tail prec tl
        | hd %:: tl@(.cons _ _) =>
          .append (reprPrec hd prec) $ .append ", " $ tail prec tl

syntax "%[" ( term ),+ "]" : term
-- Unexpanders are pain. Can't be fuqd
macro_rules
  | `(%[$hd:term]) => `(Vec.cons $hd Vec.nil)
  | `(%[$hd:term, $rest,*]) => `(Vec.cons $hd (%[ $rest,* ]))

/-- info: 10 %:: 20 %:: 30 %:: %[] : Vec ℕ (Nat.succ 0).succ.succ -/
#guard_msgs in #check %[10, 20, 30]

def Vec.lookup : Fin2 n → Vec T n → T
  | .fz, hd %:: tl => hd
  | .fs v,  _ %:: tl => tl.lookup v

def Vec.set : Fin2 n → Vec T n → T → Vec T n
  | .fz,     _ %:: tl, v => v %:: tl
  | .fs idx, hd %:: tl, v => hd %:: tl.set idx v

theorem Vec.set.overwrite {v : Vec T n}
    : (v.set idx x).set idx y = v.set idx y :=
  match v, idx with
  | hd %:: _, .fz => rfl
  | hd %:: tl, .fs _ => by
    dsimp [set]
    rw [overwrite]

theorem Vec.set.comm_ne {v : Vec T n} (hNe : idx ≠ jdx)
    : (v.set idx x).set jdx y = (v.set jdx y).set idx x :=
  match v, idx, jdx with
  | hd %:: tl, .fs _, .fs _ => by
    dsimp [set]
    rw [Vec.set.comm_ne]
    exact hNe ∘ (·.rec rfl)
  | _ %:: _, .fz, .fs _ | _ %:: _, .fs _, .fz => rfl
  | _ %:: _, .fz, .fz => (hNe rfl).elim

def Vec.set_many (v : Vec T n) : List (Fin2 n × T) → Vec T n
  | [] => v
  | ⟨idx, x⟩ :: tl => (v.set idx x).set_many tl

def Vec.set_many.perm {l₁ : List (Fin2 n × T)} {v : Vec T n}
    (hNoDup : l₁.map Prod.fst |>.Nodup)
    (hPerm : List.Perm l₁ l₂)
    : v.set_many l₁ = v.set_many l₂ := by
  induction hPerm generalizing v
  case cons el _ ih =>
    rename_i tl₁ _
    rcases hNoDup with (_|⟨hhd, hNoDup⟩)
    simp only [set_many]
    exact ih hNoDup
  case swap x y ls =>
    rcases x with ⟨xk, xv⟩
    rcases y with ⟨yk, yv⟩
    rcases hNoDup with (_|⟨hhd, hnodup⟩)
    simp only [List.map_cons, List.mem_cons, List.mem_map, Prod.exists, exists_and_right,
      exists_eq_right, ne_eq, forall_eq_or_imp, forall_exists_index] at hhd
    rcases hhd with ⟨neq, _⟩
    dsimp [set_many]
    rw [Vec.set.comm_ne neq]
  case trans a _ iha ihb =>
    rename_i l₁ l₂ l₃ _
    calc
      _ = v.set_many l₂ := iha hNoDup
      _ = v.set_many _  := ihb $ (List.Perm.nodup_iff $ List.Perm.map _ a).mp hNoDup
  case nil => rfl

def Vec.map (f : α → β) : Vec α n → Vec β n
  | %[] => %[]
  | hd %:: tl => f hd %:: tl.map f

instance : Functor (Vec · n) where map := Vec.map
instance : LawfulFunctor (Vec · n) where
  id_map x := by
    induction x
    · rfl
    next ih =>
      dsimp [Functor.map, Vec.map] at ih ⊢
      rw [ih]
  comp_map f g x := by
    induction x
    · rfl
    · next ih =>
      dsimp [Functor.map, Vec.map] at ih ⊢
      rw [ih]
  map_const := rfl

def Vec.append : Vec T n → Vec T k → Vec T (k + n)
  | %[], rst => rst
  | hd %:: tl, rst => hd %:: tl.append rst

instance : HAppend (Vec T n) (Vec T k) (Vec T (k + n)) := ⟨Vec.append⟩

theorem lookup_append_right {v2 : Vec T k} {v1 : Vec T n}
    : v1.lookup idx = (v2.append v1).lookup (idx.add k) :=
  match v2 with
  | %[] => by simp [Vec.append]; rfl
  | _ %:: _ => by
    simp only [Vec.lookup, Nat.add_eq]
    exact lookup_append_right

theorem lookup_append_left {v2 : Vec T k} {v1 : Vec T n}
    : v1.lookup idx = (v1.append v2).lookup (idx.left k) :=
  match v1, idx with
  | _ %:: _, .fz => by simp only [Vec.lookup]
  | _ %:: _, .fs _ => by
    dsimp only [Vec.lookup]
    exact lookup_append_left
  | %[], x => by cases x

@[ext]
def Vec.ext {s1 s2 : Vec T n}
    (h : s1.lookup = s2.lookup)
    : s1 = s2 :=
  match n, s1, s2 with
  | 0,  %[], %[] => rfl
  | n+1, h₁ %:: t₁, h₂ %:: t₂ => by
    have := Function.funext_iff.mp h
    obtain rfl := this .fz
    simp only [lookup, cons.injEq, true_and]
    exact Vec.ext $ funext λ x ↦ this $ .fs x

