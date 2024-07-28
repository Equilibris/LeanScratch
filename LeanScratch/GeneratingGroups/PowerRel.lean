import LeanScratch.GeneratingGroups.Iso

def PowerRel.section : GGMod.GG α → GGMod.GG (α × ℕ)
  | .unit => .unit
  | .obj a => .obj (a, 1)
  | .inv a => .inv (a, 1)
  | .app a b => .app (PowerRel.section a) (PowerRel.section b)
def PowerRel.retraction :  GGMod.GG (α × ℕ) → GGMod.GG α
  | .unit | .obj (_, 0) | .inv (_, 0)=> .unit
  | .obj (a, n+1) => .app (.obj a) (PowerRel.retraction (.obj (a, n)))
  | .inv (a, n+1) => .app (.inv a) (PowerRel.retraction (.inv (a, n)))
  | .app a b => .app (PowerRel.retraction a) (PowerRel.retraction b)

inductive PowerRel (R : GGMod.rTy α) : GGMod.rTy (α × ℕ)
  | lift : R a b → PowerRel R (PowerRel.section a) (PowerRel.section b)
  | objIn : PowerRel R (.app (.obj (a, n)) (.obj (a, m))) (.obj (a, n + m))
  | invIn : PowerRel R (.app (.inv (a, n)) (.inv (a, m))) (.inv (a, n + m))
  | objDisolve : PowerRel R (.obj (a, 0)) .unit
  | invDisolve : PowerRel R (.inv (a, 0)) .unit

theorem PowerRel.secRelInv.{u_1} {α : Type u_1} {R : GGMod.rTy α} {x : GGMod.GG (α × ℕ)} :
    GGMod.Rel (PowerRel R) ((PowerRel.section ∘ retraction) x) x := by
  induction x using retraction.induct
  <;> simp_all [Function.comp, Nat.succ_eq_add_one, retraction, PowerRel.section]
  · exact .refl
  · exact .symm (.base .objDisolve)
  · exact .symm (.base .invDisolve)
  case case4 ih =>
    rw [Nat.add_comm]
    exact .trans (.homo .refl ih) (.base .objIn)
  case case5 ih =>
    rw [Nat.add_comm]
    exact .trans (.homo .refl ih) (.base .invIn)

  case case6 aih bih => exact .homo aih bih

theorem PowerRel.relSecInv.{u_1} {α : Type u_1} {R : GGMod.rTy α} {x : GGMod.GG α} :
  GGMod.Rel R ((retraction ∘ PowerRel.section) x) x := by
  induction x using section.induct
  <;> simp_all [Function.comp, PowerRel.section, retraction]
  · exact .refl
  · exact .appUnit
  · exact .appUnit
  case case4 aih bih => exact .homo aih bih

open PowerRel in
open GGMod in
theorem PowerRel.Iso : PowerRel R ≅ R := by
  apply GGMod.Iso.Alt
  use PowerRel.retraction
  use PowerRel.section
  constructor
  · introv h
    induction h
    <;> try simp only [retraction]
    · exact .appUnit
    · exact .unitApp
    case objInv h =>
      rcases h with ⟨w, p⟩
      induction p
      <;> simp only [retraction]
      exact .appUnit
      rename_i n h

      have : GGMod.Rel R (.app (.obj w) (retraction (.obj (w, n)))) (.app (retraction (.obj (w, n))) (.obj w)) := by
        clear *-n
        induction n
        <;> simp only [retraction, GGMod.assoc]
        · open GGMod (GG) in open GGMod.GG in
          calc
            GGMod.Rel R (.app (GG.obj w) .unit) (GG.obj w) := .appUnit
            GGMod.Rel R _ (.app .unit (GG.obj w)) := .symm .unitApp
        next n ih => exact .symm (.trans .assoc (.homo .refl (.symm ih)))

      open GGMod (GG) in open GGMod.GG in
      calc
        GGMod.Rel R
          (GG.app (.app (.obj w) (retraction (.obj (w, n)))) (.app (.inv w) (retraction (.inv (w, n)))))
          (GG.app (.app (retraction (.obj (w, n))) (.obj w)) (.app (.inv w) (retraction (.inv (w, n)))))
          := .homo this .refl
        GGMod.Rel R _
          (GG.app (.app (retraction (.obj (w, n))) (.app (.obj w) (.inv w))) (retraction (.inv (w, n))))
          := by
            refine .trans .assoc ?_
            refine .symm ?_
            refine .trans .assoc ?_
            refine .homo .refl .assoc
        GGMod.Rel R _
          (GG.app (.app (retraction (.obj (w, n))) (.unit)) (retraction (.inv (w, n))))
          := .homo (.homo .refl .objInv) .refl
        GGMod.Rel R _
          (GG.app (retraction (.obj (w, n))) (retraction (.inv (w, n))))
          := .homo .appUnit .refl
        GGMod.Rel R _ GG.unit := h
    case invObj h =>
      rcases h with ⟨w, p⟩
      induction p
      <;> simp only [retraction]
      exact .appUnit
      rename_i n h

      have : GGMod.Rel R (.app (.inv w) (retraction (.inv (w, n)))) (.app (retraction (.inv (w, n))) (.inv w)) := by
        clear *-n
        induction n
        <;> simp only [retraction, GGMod.assoc]
        · open GGMod (GG) in open GGMod.GG in
          calc
            GGMod.Rel R (.app (GG.inv w) .unit) (GG.inv w) := .appUnit
            GGMod.Rel R _ (.app .unit (GG.inv w)) := .symm .unitApp
        next n ih => exact .symm (.trans .assoc (.homo .refl (.symm ih)))

      open GGMod (GG) in open GGMod.GG in
      calc
        GGMod.Rel R
          (GG.app (.app (.inv w) (retraction (.inv (w, n)))) (.app (.obj w) (retraction (.obj (w, n)))))
          (GG.app (.app (retraction (.inv (w, n))) (.inv w)) (.app (.obj w) (retraction (.obj (w, n)))))
          := .homo this .refl
        GGMod.Rel R _
          (GG.app (.app (retraction (.inv (w, n))) (.app (.inv w) (.obj w))) (retraction (.obj (w, n))))
          := by
            refine .trans .assoc ?_
            refine .symm ?_
            refine .trans .assoc ?_
            refine .homo .refl .assoc
        GGMod.Rel R _
          (GG.app (.app (retraction (.inv (w, n))) (.unit)) (retraction (.obj (w, n))))
          := .homo (.homo .refl .invObj) .refl
        GGMod.Rel R _
          (GG.app (retraction (.inv (w, n))) (retraction (.obj (w, n))))
          := .homo .appUnit .refl
        GGMod.Rel R _ GG.unit := h

    · exact .assoc
    case trans a b => exact .trans a b
    case symm a => exact .symm a
    · exact .refl
    case base h =>
      induction h
      case lift a b h =>
        calc
          GGMod.Rel R (retraction (PowerRel.section a)) a := relSecInv
          GGMod.Rel R a b := .base h
          GGMod.Rel R _ (retraction (PowerRel.section b)) := .symm relSecInv
      case objIn a b h n m  =>
        induction n
        · simp only [retraction, Nat.zero_add]
          exact .unitApp
        next n ihn =>
        rw [Nat.add_assoc, Nat.add_comm 1, ←Nat.add_assoc]
        simp only [retraction] at ihn ⊢
        exact .trans .assoc (.homo .refl ihn)
      case invIn a b h n m  =>
        induction n
        · simp only [retraction, Nat.zero_add]
          exact .unitApp
        next n ihn =>
        rw [Nat.add_assoc, Nat.add_comm 1, ←Nat.add_assoc]
        simp only [retraction] at ihn ⊢
        exact .trans .assoc (.homo .refl ihn)
      · simp only [retraction]
        exact .refl
      · simp only [retraction]
        exact .refl
    case homo a b => exact .homo a b
  constructor
  · introv h
    induction h
    <;> try simp only [PowerRel.section]
    case appUnit   => exact .appUnit
    case unitApp   => exact .unitApp
    case objInv    => exact .objInv
    case invObj    => exact .invObj
    case assoc     => exact .assoc
    case trans a b => exact .trans a b
    case symm  a   => exact .symm a
    case refl      => exact .refl
    case base  h   => exact .base (.lift h)
    case homo  a b => exact .homo a b
  constructor
  · introv
    simp only [retraction]
    exact .refl
  exact ⟨secRelInv, relSecInv⟩

