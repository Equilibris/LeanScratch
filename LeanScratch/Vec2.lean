import LeanScratch.Vec

def Vec2 (T : Type u) (n : Nat) := Fin2 n → T

def Vec2.nil {T} : Vec2 T 0 := Fin2.elim0
def Vec2.cons (h : T) (tl : Vec2 T n) : Vec2 T n.succ
  | .fz => h
  | .fs v => tl v

notation:20 "%![]" => Vec2.nil
syntax "%![" ( term ),+ "]" : term

macro_rules
  | `(%![$hd:term]) => `(Vec2.cons $hd Vec2.nil)
  | `(%![$hd:term, $rest,*]) => `(Vec2.cons $hd (%![ $rest,* ]))

theorem Vec2.eqCons (v : Vec2 T (n + 1)) : v = Vec2.cons (v .fz) (v ∘ .fs) := funext $ fun
    | .fz   => rfl
    | .fs _ => rfl

instance : Unique (Vec2 T 0) := ⟨⟨Vec2.nil⟩, fun _ => funext Fin2.elim0⟩

@[elab_as_elim]
def Vec2.recv {T : Type u}
    {motive : (a : ℕ) → Vec2 T a → Sort u_1}
    (z : motive 0 Vec2.nil)
    (s : {n : ℕ} → (hd : T) → (tl : Vec2 T n) → motive n tl → motive n.succ (Vec2.cons hd tl))
    {a : ℕ} (t : Vec2 T a)
    : motive a t :=
  match a with
  | 0 => (Unique.uniq _ t).symm.rec z
  | _+1 => (congrArg _ $ eqCons t).mpr
    $ s _ _
    $ Vec2.recv z s $ t ∘ Fin2.fs

def Vec2.toVec (v2 : Vec2 T n) : Vec T n := match n with
  | 0 => %[]
  | _ + 1 => v2 .fz %:: Vec2.toVec (v2 ∘ Fin2.fs)

instance : Equiv (Vec2 T n) (Vec T n) where
  toFun := Vec2.toVec
  invFun x := (Vec.lookup · x)
  left_inv := fun v => by
    induction v using Vec2.recv <;> funext x <;> cases x
    case fz => rfl
    case fs ih z => exact Function.funext_iff.mp ih z
  right_inv := fun v => v.rec rfl (fun _ _ ih => (Vec.cons.injEq _ _ _ _).mpr ⟨rfl, ih⟩)

def Vec2.map (f : α → β) (base : Vec2 α n) : Vec2 β n := f ∘ base

instance : Functor (Vec2 · n) where map := Vec2.map

instance : LawfulFunctor (Vec2 · n) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

def Vec2.Mem (x : T) (v : Vec2 T n) : Prop := ∃ idx, v idx = x
@[simp]
def Vec2.Mem_toVec {v : Vec2 T n} (h : Vec2.Mem x v) : Vec.Mem x v.toVec := by
  rcases h with ⟨idx, h⟩
  induction idx generalizing x
  <;> dsimp [toVec]
  case fz =>
    subst h
    exact .head _
  case fs ih =>
    exact .tail _ (@ih _ (v ∘ .fs) h)
