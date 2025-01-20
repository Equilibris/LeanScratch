import LeanScratch.Fin2

inductive Vec (T : Type u) : Nat → Type u
  | nil : Vec T 0
  | cons (hd : T) (tl : Vec T n) : Vec T n.succ

infixr:20 " %:: " => Vec.cons
notation:20 "%[]" => Vec.nil

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

