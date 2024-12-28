namespace Consistent

-- Define the propositional formulas
inductive Form where
| 𝕡 : Form
| 𝕢 : Form
| _true : Form
| _false : Form
| implies : Form → Form → Form

open Form

infixr:10 "⇒" => implies

-- Define the unit type (⊤)
inductive Unit where
| tt : Unit

open Unit
notation "⊤" => Unit

-- Define the empty type (⊥)
inductive Empty where
notation "⊥" => Empty

-- Negation
def Not (A : Type) : Type := A → ⊥
notation "¬" A => Not A

-- Validity of a formula (i.e., `Valid A` means `A` is always true)
def Valid : Form → Type
| 𝕡 => ⊥
| 𝕢 => ⊥
| _true => ⊤
| _false => ⊥
| (implies A B) => Valid A → Valid B

-- Example: formula `𝕡 ⇒ 𝕡` is valid
def id : Valid (𝕡 ⇒ 𝕡) := λ z => z

-- Observe: formula `_false` is not valid
def falseNotValid : ¬ Valid _false := 
  λ h => h

-- Provability of a formula (i.e., `Proof A` means formula `A` is derivable)
inductive Proof : Form → Type where
| T : Proof _true
| K : {A B : Form} → Proof (A ⇒ B ⇒ A)
| S : {A B C : Form} → Proof ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C))
| MP : {A B : Form} → Proof (A ⇒ B) → Proof A → Proof B

open Proof

-- Example: formula `𝕡 ⇒ 𝕡` is provable
def id' : Proof (𝕡 ⇒ 𝕡) :=
  MP (MP S K) (@K 𝕡 𝕢)

def translate : Proof f → Valid f
  | .T => .tt
  | .K => fun a _ => a
  | .S => fun long short a => long a (short a)
  | .MP ffn farg => (translate ffn) (translate farg)

-- Show: `false` is not provable
-- TODO
def consistent : ¬ Proof _false := translate

end Consistent
