import Mathlib.Data.Rel
import Mathlib.Logic.Relation

abbrev endoRel (α : Type _) := α → α → Prop

namespace GGMod
@[aesop safe [constructors, cases]]
inductive GG (α : Type _)
  | unit
  | obj (v : α)
  | inv (v : α)
  | app (a b : GG α)

instance : Inhabited (GG α) := ⟨.unit⟩

/- def normApp : GG α → GG α -/
/-   | x@(.unit) | x@(.inv _) | x@(.obj _) => x -/
/-   | .app (.app a b) c => .app a (normApp (.app b c)) -/
/-   | .app a b => .app a (normApp b) -/

/- def normInvs : GG α → GG α -/
/-   | x@(.unit) | x@(.inv _) | x@(.obj _) => x -/
/-   | x@(.app (.obj a) (.inv b)) | x@(.app (.inv a) (.obj b))  => if a = b then .unit else x -/
/-   | -/

abbrev rTy α := endoRel (GG α)

@[aesop safe [constructors, cases]]
inductive Rel (R : rTy α) : GG α → GG α → Prop
  | appUnit : Rel R (.app v .unit) (v)
  | unitApp : Rel R (.app .unit v) (v)
  | objInv : Rel R (.app (.obj a) (.inv a)) .unit
  | invObj : Rel R (.app (.inv a) (.obj a)) .unit
  | assoc : Rel R (.app (.app a b) c) (.app a (.app b c))
  | trans : Rel R a b → Rel R b c → Rel R a c
  | symm : Rel R a b → Rel R b a
  | refl : Rel R a a

  | base : R a b → Rel R a b
  | homo : Rel R a₁ a₂ → Rel R b₁ b₂ → Rel R (.app a₁ b₁) (.app a₂ b₂)

instance : Trans (Rel R) (Rel R) (Rel R) where trans a b := .trans a b

instance base (R : rTy α): Setoid (GG α) where
  r := Rel R
  iseqv := {
    refl := fun _ => .refl,
    trans := .trans,
    symm := .symm
  }

def RelSum (a b : α → β → Prop) (x : α) (y : β) := a x y ∨ b x y
end GGMod

open GGMod in
abbrev GGMod {α : Type u} (R : GG α → GG α → Prop) : Type u := Quotient (base R)

instance : Trans (@Eq (GGMod R)) (@Eq (GGMod R)) (@Eq (GGMod R)) where
  trans := by
    introv h₁ h₂
    exact h₁.trans h₂

namespace GGMod

def enter { R : rTy α} (x : GG α) : GGMod R :=
  Quotient.mk (base R) x

section
variable {α : Type u} {R : rTy α}

def app (a b : GGMod R) : GGMod R :=
  Quotient.lift₂ (fun a b => Quotient.mk (base R) (GG.app a b)) (by
    introv aeq beq
    simp only
    apply Quotient.sound'

    simp only [HasEquiv.Equiv, Setoid.r, base] at *
    exact .homo aeq beq
  ) a b

def obj (a : α) : GGMod R := Quotient.mk (base R) (.obj a)
def inv (a : α) : GGMod R := Quotient.mk (base R) (.inv a)
def unit : GGMod R := Quotient.mk (base R) .unit

@[simp]
theorem appUnit : app a unit = a := by
  unfold app
  induction a using Quotient.inductionOn
  apply Quotient.sound
  exact .appUnit
@[simp]
theorem unitApp : app unit a = a := by
  unfold app
  induction a using Quotient.inductionOn
  apply Quotient.sound
  exact .unitApp
@[simp]
theorem objInv : @app _ R (obj a) (inv a) = unit := by
  unfold app unit
  apply Quotient.sound
  exact .objInv
@[simp]
theorem invObj : @app _ R (inv a) (obj a) = unit := by
  unfold app
  apply Quotient.sound
  exact .invObj

/- theorem base (R a b) : a = b -/
end
@[simp]
theorem assoc : @app _ R (app a b) c = app a (app b c) := by
  unfold app
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  induction c using Quotient.inductionOn
  apply Quotient.sound
  exact .assoc

instance : Inhabited (GGMod R) := ⟨unit⟩

abbrev homo {R : rTy α} {R' : rTy β} (f : GGMod R → GGMod R') :=
  ∀ a b, f (.app a b) = .app (f a) (f b)

theorem homoComp {R₁ : rTy α} {R₂ : rTy β} {R₃ : rTy β} {f : GGMod R₁ → GGMod R₂} {g : GGMod R₂ → GGMod R₃} (h₁ : homo f) (h₂ : homo g) : homo (g ∘ f) := by
  unfold homo Function.comp
  introv
  rw [h₁, h₂]

def Iso (R : rTy α) (R' : rTy β) : Prop := ∃f : GGMod R → GGMod R', homo f ∧ Function.Bijective f

infix:20 " ≅ " => Iso

theorem Iso.Alt {R : rTy α} {R' : rTy β} :
    (∃ f : GG α → GG β, ∃ f' : GG β → GG α,
      (∀ {x y}, (Rel R) x y → (Rel R') (f x) (f y)) ∧
      (∀ {x y}, (Rel R') x y → (Rel R) (f' x) (f' y)) ∧
      (∀ {a b}, (Rel R') (f (.app a b)) (.app (f a) (f b))) ∧
      (∀ {x}, (Rel R) ((f' ∘ f) x) (x) ) ∧
      (∀ {x}, (Rel R') ((f ∘ f') x) (x) )
      ) → (R ≅ R') := by
  rintro ⟨f, f', fLaw, f'Law, homo, bijL, bijR⟩
  use fun x =>
    @Quotient.mk _ (base R') (f (@Quotient.out _ (base R) x))

  constructor
  · unfold GGMod.homo
    introv
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    rename_i a b
    simp only [app, Quotient.lift_mk, Quotient.eq]

    have := fLaw (@Quotient.mk_out _ (base R) (.app a b))
    have a := fLaw (@Quotient.mk_out _ (base R) a)
    have b := fLaw (@Quotient.mk_out _ (base R) b)
    simp only [Function.comp, HasEquiv.Equiv, Setoid.r] at bijR this ⊢

    exact .trans this (.trans homo (.homo a.symm b.symm))

  · apply Function.bijective_iff_has_inverse.mpr
    use fun x =>
      @Quotient.mk _ (base R) (f' (@Quotient.out _ (base R') x))
    constructor
    · simp only [Function.LeftInverse]
      introv
      induction x using Quotient.inductionOn
      rename_i x
      simp only [Quotient.eq]
      have inner :=  @Quotient.mk_out _ (base R) x
      have outer :=  @Quotient.mk_out _ (base R') (f (@Quotient.out _ (base R) (@Quotient.mk _ (base R) x) ))
      simp only [Function.comp, HasEquiv.Equiv, Setoid.r] at bijL inner outer ⊢

      exact .trans (f'Law outer) (.trans bijL inner)

    · simp only [Function.RightInverse, Function.LeftInverse]
      introv
      induction x using Quotient.inductionOn
      rename_i x
      simp only [Quotient.eq]
      have inner :=  @Quotient.mk_out _ (base R') x
      have outer :=  @Quotient.mk_out _ (base R) (f' (@Quotient.out _ (base R') (@Quotient.mk _ (base R') x) ))
      simp only [Function.comp, HasEquiv.Equiv, Setoid.r] at bijR inner outer ⊢

      exact .trans (fLaw outer) (.trans bijR inner)

theorem isoRfl : R ≅ R := by
  use id
  constructor
  · unfold homo
    introv
    simp only [id]
  · exact Function.bijective_id

open Function in
theorem isoSymm {R : rTy α} {R' : rTy β} {h : R ≅ R'} : R' ≅ R := by
  rcases h with ⟨w, p⟩
  use invFun w
  have rInv := rightInverse_invFun $ Bijective.surjective p.right
  have lInv := leftInverse_invFun  $ Bijective.injective p.right
  constructor
  · unfold homo
    introv
    change id (invFun w (a.app b)) = id ((invFun w a).app (invFun w b))
    have rInvId := RightInverse.id rInv
    have lInvId := LeftInverse.id lInv
    rw [lInvId.symm]
    have (a) : w (invFun w a) = a := by
      change _ = id a
      rw [←rInvId]
      simp only [comp_apply]

    unfold Function.comp
    conv =>
      rhs
      rw [p.left, this a, this b]
    rw [this]

  · apply bijective_iff_has_inverse.mpr
    use w
    constructor
    · exact rInv
    · exact lInv

theorem isoTrans {R₁ : rTy α} {R₂ : rTy β} {R₃ : rTy β} {h₁₂ : R₁ ≅ R₂} {h₂₃ : R₂ ≅ R₃} : R₁ ≅ R₃ := by
  rcases h₁₂ with ⟨w₁₂, p₁₂⟩
  rcases h₂₃ with ⟨w₂₃, p₂₃⟩
  use w₂₃ ∘ w₁₂
  constructor
  · exact homoComp p₁₂.left p₂₃.left
  · apply Function.Bijective.comp p₂₃.right p₁₂.right

end GGMod

inductive REqGen (R : α → α → Prop) : α → α → Prop
  | base : R a b → REqGen R a b
  | refl : REqGen R a a
  | trans : REqGen R a b → REqGen R b c → REqGen R a c
  | symm : REqGen R a b → REqGen R b a

def EqGenSetoid (R : α → α → Prop) : Setoid α where
  r := REqGen R
  iseqv := {
    refl := fun _ => .refl,
    symm := .symm,
    trans := .trans,
  }


def K : GGMod.rTy α := fun _ _ => True
def E : GGMod.rTy Empty := fun _ _ => False
theorem K.KillSingular { α } : @K α ≅ E := by
  use fun _ => GGMod.unit
  constructor
  · unfold GGMod.homo
    introv
    simp only [GGMod.appUnit]
  · apply Function.bijective_iff_has_inverse.mpr
    use fun _ => GGMod.unit
    simp only [Function.LeftInverse, Function.RightInverse]
    constructor
    <;> introv
    <;> induction x using Quotient.inductionOn
    <;> apply Quotient.sound
    <;> simp only [HasEquiv.Equiv, Setoid.r]
    · exact .base True.intro
    · rename_i x
      induction x
      · exact .refl
      · trivial
      · trivial
      case app a_ih b_ih =>
        exact .symm (.trans (.homo a_ih.symm b_ih.symm) .appUnit)

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


open GGMod in
def fn.f {R : rTy α}: GGMod.GG (α × ℕ) → GGMod R
  | .unit | .obj (_, 0) | .inv (_, 0)=> unit
  | .obj (a, n+1) => app (obj a) (f (.obj (a, n)))
  | .inv (a, n+1) => app (inv a) (f (.inv (a, n)))
  | .app a b => app (f a) (f b)
open GGMod in
noncomputable def fn (v : GGMod (PowerRel R)) : GGMod R :=
  let x := @Quotient.out _ (base (PowerRel R)) v
  let x := PowerRel.retraction x
  .enter x

open GGMod in
def fn' (v : GGMod (PowerRel R)) : GGMod R :=
  v.lift fn.f (by
    introv h
    induction h
    <;> try simp only [fn.f, appUnit, unitApp]

    case objInv h =>
      rcases h with ⟨w, p⟩
      induction p
      <;> simp only [fn.f, appUnit, assoc]
      rename_i n h

      have : (@GGMod.app _ R (obj w) (fn.f (.obj (w, n)))) = (GGMod.app (fn.f (.obj (w, n))) (obj w)) := by
        clear *-n
        induction n
        <;> simp only [fn.f, appUnit, unitApp, assoc]
        congr 1

      calc
        GGMod.app (obj w) (.app (fn.f (.obj (w, n))) (.app (.inv w) (fn.f (.inv (w, n))))) =
          GGMod.app (.app (obj w) (fn.f (.obj (w, n)))) (.app (.inv w) (fn.f (.inv (w, n))))
          := by simp only [assoc]
        _ = GGMod.app (.app (fn.f (.obj (w, n))) (obj w)) (.app (.inv w) (fn.f (.inv (w, n)))) := by rw [this]
        _ = GGMod.app (.app (fn.f (.obj (w, n))) (.app (obj w) (.inv w))) (fn.f (.inv (w, n))) := by simp only [assoc]
        _ = GGMod.app (fn.f (.obj (w, n))) (fn.f (.inv (w, n))) := by simp only [objInv, appUnit]
        _ = GGMod.unit := by rw [h]

    case invObj h =>
      rcases h with ⟨w, p⟩
      induction p
      <;> simp only [fn.f, appUnit, assoc]
      rename_i n h

      have : (@GGMod.app _ R (inv w) (fn.f (.inv (w, n)))) = (GGMod.app (fn.f (.inv (w, n))) (inv w)) := by
        clear *-n
        induction n
        <;> simp only [fn.f, appUnit, unitApp, assoc]
        congr 1

      calc
        GGMod.app (inv w) (.app (fn.f (.inv (w, n))) (.app (.obj w) (fn.f (.obj (w, n))))) =
          GGMod.app (.app (inv w) (fn.f (.inv (w, n)))) (.app (.obj w) (fn.f (.obj (w, n))))
          := by simp only [assoc]
        _ = GGMod.app (.app (fn.f (.inv (w, n))) (inv w)) (.app (.obj w) (fn.f (.obj (w, n)))) := by rw [this]
        _ = GGMod.app (.app (fn.f (.inv (w, n))) (.app (inv w) (.obj w))) (fn.f (.obj (w, n))) := by simp only [assoc]
        _ = GGMod.app (fn.f (.inv (w, n))) (fn.f (.obj (w, n))) := by simp only [invObj, appUnit]
        _ = GGMod.unit := by rw [h]

    case assoc =>  simp only [fn.f, GGMod.assoc]
    case trans a b => exact a.trans b
    case symm x => exact x.symm
    case homo => simp_all only
    case base a' b' h =>
      induction h
      case lift a b h =>
        sorry
        /- induction a using PowerRel.section.induct -/
        /- <;> induction b using PowerRel.section.induct -/
        /- <;> simp_all [PowerRel.section, fn.f, appUnit, unit, app, inv] -/
        /- · sorry -/
        /- · sorry -/
        /- · sorry -/
        /- · sorry -/
        /- · sorry -/
        /- try exact .base h -/

      case objIn n m =>
        induction n
        <;> simp only [fn.f, unitApp, Nat.zero_add, assoc]
        rename_i n h
        conv at h => lhs; simp only [fn.f]
        rw [h, Nat.add_assoc n 1, Nat.add_comm 1, ←Nat.add_assoc]
        conv => rhs; simp only [fn.f]
      case invIn n m => 
        induction n
        <;> simp only [fn.f, unitApp, Nat.zero_add, assoc]
        rename_i n h
        conv at h => lhs; simp only [fn.f]
        rw [h, Nat.add_assoc n 1, Nat.add_comm 1, ←Nat.add_assoc]
        conv => rhs; simp only [fn.f]
      case objDisolve => simp [fn.f]
      case invDisolve => simp [fn.f]
  )

open GGMod in
def fn₁.f {R : rTy (α × ℕ)}: GGMod.GG α → GGMod R
  | .unit => unit
  | .app a b => app (fn₁.f a) (fn₁.f b)
  | .inv a => .inv (a, 1)
  | .obj a => .obj (a, 1)
open GGMod in

/- #print Quotient.out -/

noncomputable def fn₁ (v : GGMod R) : GGMod (PowerRel R) :=
  let x := @Quotient.out _ (base R) v
  let x := PowerRel.section x
  .enter x
  /- v.lift fn₁.f (by -/
  /-   introv h -/
  /-   cases h -/
  /-   <;> try simp only [fn₁.f, appUnit, unitApp, objInv, invObj, assoc] -/
  /-   case trans => sorry -/
  /-   case symm => sorry -/
  /-   case base => sorry -/
  /-   case homo => sorry -/
  /-   ) -/

open GGMod in
open PowerRel in
/- theorem RetractionLawful : -/
/-  @Quotient.mk _ (base (PowerRel R)) (retraction (Quotient.out (Quotient.mk (base (PowerRel R)) (.app a b)))) =  sorry := sorry -/


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
    · exact .appUnit
    · exact .unitApp
    · exact .objInv
    · exact .invObj
    · exact .assoc
    case trans a b => exact .trans a b
    case symm a => exact .symm a
    · exact .refl
    case base a b h =>
      exact .base (.lift h)
    case homo a b => exact .homo a b
  constructor
  · introv
    simp only [retraction]
    exact .refl
  exact ⟨secRelInv, relSecInv⟩
  /- unfold GGMod.Iso -/
  /- use fn -/
  /- constructor -/
  /- · unfold GGMod.homo -/
  /-   introv -/
  /-   induction a using Quotient.inductionOn -/
  /-   induction b using Quotient.inductionOn -/
  /-   rename_i a b -/
  /-   simp only [fn, GGMod.app, Quotient.lift_mk, fn.f, GGMod.enter] -/
  /-   apply Quotient.sound -/
  /-   let z := a.app b -/
  /-   have : z = a.app b := rfl -/
  /-   rw [←this] -/
  /-   let x := @Quotient.mk_out _ (GGMod.base (PowerRel R)) z -/
  /-   simp [HasEquiv.Equiv, Setoid.r] at x ⊢ -/
  /-   induction @Quotient.out _ (GGMod.base (PowerRel R)) ⟦z⟧ using retraction.induct -/
  /-   <;> simp [retraction] -/

  /- · sorry -/

