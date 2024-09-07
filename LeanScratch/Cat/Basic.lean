import Mathlib.Init.Set
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.ExtractGoal

class Cat (obj : Type _) where
  mor : obj → obj → Type _

  id : (o : obj) → mor o o
  comp : mor a b → mor b c → mor a c

  IdLeft  : ∀ f : mor a b, comp (id a) f = f 
  IdRight : ∀ f : mor a b, comp f (id b) = f 
  Assoc : ∀ f : mor a b, ∀ g : mor b c, ∀ h : mor c d, comp f (comp g h) = comp (comp f g) h 

infixr:90 " ⊚ "  => Cat.comp

instance type : Cat (Type u) where
  mor := fun a b => a → b
  id  := fun o v => v
  comp := fun f g v => by
    dsimp at f g
    exact g (f v)

  IdLeft  := by simp
  IdRight := by simp
  Assoc := by simp

class CFunctor (inC : Cat α) (outC : outParam (Cat β)) where
  om   : α → β
  mMap : inC.mor a b → outC.mor (om a) (om b)

  IdToId : ∀ o, mMap (inC.id o) = outC.id (om o)
  Dist : ∀ f : inC.mor a b, ∀ g : inC.mor b c, mMap (f ⊚ g) = (mMap f) ⊚ (mMap g)

instance idF : CFunctor a a where
  om := id
  mMap := id
  IdToId := by simp
  Dist := by simp

def compF {α : Type u_1} {a b c : Cat α} (x : CFunctor a b) (y : CFunctor b c) : CFunctor a c where
  om := y.om ∘ x.om
  mMap := y.mMap ∘ x.mMap
  IdToId := by
    intro o
    dsimp
    rw [x.IdToId, y.IdToId]
  Dist := by
    intro _ _ _ f g
    dsimp
    rw [x.Dist, y.Dist]

instance cat : Cat (Cat α) where
  mor := CFunctor
  id := fun a => idF

  comp := compF
  IdLeft := by
    intros a b f
    simp only [compF, Function.comp_apply]
    congr
  IdRight := by
    intros a b f
    simp only [compF, Function.comp_apply]
    congr
  Assoc := by
    intros a b c d f g h
    simp only [compF, Function.comp_apply]
    congr

def isomorphism [c : Cat α] (x : c.mor a b) (y : c.mor b a) : Prop :=
  c.comp x y = c.id a ∧ c.comp y x = c.id b

theorem EquivIsomorphism (x : Equiv a b) : isomorphism (c := type) x.toFun x.invFun := by
  constructor
  · sorry
  · sorry

instance set : Cat ((a : Type _) × Set a) where
  mor := fun ⟨a, _⟩ ⟨b, _⟩ => a → b
  id := fun ⟨t, _⟩ => @id t
  comp := fun f g => g ∘ f
  IdLeft := by
    intros a b f
    ext x
    simp only [Function.comp_apply, id_eq]
  IdRight := by
    intros a b f
    ext x
    simp only [Function.comp_apply, id_eq]
  Assoc := by
    intro a b c d f g h
    ext x
    simp only [Function.comp_apply]

