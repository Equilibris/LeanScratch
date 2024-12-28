-- Forwards lists grow on the left
-- Mnemonic: > indicates the forward direction
inductive ListF : (A : Type) → Type where
  | nil : ListF A
  | cons : A → ListF A → ListF A

open ListF
infixr:5 ":>" => cons

-- Backwards lists grow on the right
-- Mnemonic: < indicates the backward direction
inductive ListB : (A : Type) → Type where
  | lin : ListB A
  | snoc : ListB A → A → ListB A

open ListB
infixl:5 ":<" => snoc

------------------------------------------------------------------------
-- Combining lists
--
-- There are two ways to combine forwards & backwards lists in an
-- order-preserving manner depending on the output type.

-- 1. Fish
-- Mnemonic: _<><_ takes a backwards (<) and a forwards (>) list and
-- returns a backwards one (<)

-- TODO:
def fish (sx : ListB A) (xs : ListF A) : ListB A :=
  match xs with
  | .nil => sx
  | .cons v xs => fish sx xs :< v

-- Make `fish` look like a fish
infixl:5 "<><" => fish

-- 2. Chips
-- Mnemonic: _<>>_ takes a backwards (<) and a forwards (>) list and
-- returns a forwards one (>)

-- TODO:
def chips (sx : ListB A) (xs : ListF A) : ListF A := 
  match sx with
  | .lin => xs
  | sx :< v => v :> chips sx xs

infixr:5 "<>>" => chips

------------------------------------------------------------------------
-- Locating an element in the middle of a forward list

-- Using these combinators we can explain what it means for an
-- element to be in focus inside of a forward list: the list
-- can be decomposed into a backward prefix chipsed onto the
-- element itself in front of a forward suffix.

inductive Lookup : {A : Type} → A → ListF A → Type where
  | found : (sx : ListB A) → (x : A) → (xs : ListF A) → Lookup x (sx <>> x :> xs)

open Lookup
notation:3 sx:3 "[" x:3 "]" xs:3 => found sx x xs

example : Lookup 1 (3 :> 2 :> 1 :> 0 :> 9 :> .nil) := (.lin :< 2 :< 3)[1](0 :> 9 :> .nil)

------------------------------------------------------------------------
-- Pointwise lifting a predicate over a forward list

-- Describing what it means for a predicate P to hold of
-- all the elements in a forwards list.
-- We overload the list constructors as the structure is
-- exactly the same:
--   1. P is trivially true of all the elements in the empty list
--   2. P is true of all the elements in the list (x :> xs) iff
--       i. it is true of x
--       ii. it is true of all the elements in xs

inductive All : (P : A → Type) → ListF A → Type where
  | nil : All P nil
  | cons : P x → All P xs → All P (x :> xs)

open All
infixl:5 ":>" => All.cons

------------------------------------------------------------------------
-- Focusing on All the elements in sight

-- Every element in a list can be focused on

-- Corrected focus.ind function
def focus.ind {A : Type} {P : A → Type} {xs : ListF A} 
  (prev) (curr )
  (ih : xs = (prev <>> curr)) : All (Lookup · xs) curr :=
  match curr with
  | .nil => .nil
  | hd :> tl =>
    .cons
      (by
        rw [ih]
        apply Lookup.found)
      (focus.ind (prev :< hd) tl (by
        rw [ih]
        simp [chips]
        rfl))

-- TODO:
def focus (xs : ListF A) : All (Lookup · xs) xs := focus.ind .lin xs rfl
