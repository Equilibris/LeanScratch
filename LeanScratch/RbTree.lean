import Mathlib.Data.Finset.Basic

/- Attucus's code:

type 'a rbtree = Leaf | Node of bool * 'a * 'a rbtree * 'a rbtree
let rec mem (x : 'a) : 'a rbtree -> bool = function
  | Leaf -> false
  | Node (_, y, l, r) -> x == y || (x < y && mem x l) || (x > y && mem x r)
let balance : bool * 'a * 'a rbtree * 'a rbtree -> 'a rbtree = function
  | true, z, Node (false, y, Node (false, x, a, b), c), d
  | true, z, Node (false, x, a, Node (false, y, b, c)), d
  | true, x, a, Node (false, z, Node (false, y, b, c), d)
  | true, x, a, Node (false, y, b, Node (false, z, c, d)) -> Node (false, y, Node (true, x, a, b), Node (true, z, c, d))
  | a, b, c, d -> Node (a, b, c, d)
let black (Node (_,y,a,b)) = Node (true, y,a,b)
let (>>) f g x = g(f(x))
let insert (x : 'a) : 'a rbtree ->  'a rbtree =
  let rec ins : 'a rbtree -> 'a rbtree = function
    | Leaf -> Node (false, x, Leaf, Leaf)
    | Node (color, y, a, b) ->
      if x < y then balance (color, y, ins a, b)  else balance (color, y, a, ins b)
  in ins >> black
-/

inductive Colour | red | black
deriving DecidableEq, Repr

inductive rbnode (α : Type _) [Ord α] [DecidableEq α] [LT α]
  | lf 
  | node (colour : Colour) (data : α) (l r : rbnode α)
deriving Repr

namespace rbnode

variable {α : Type _} [o : Ord α] [e : DecidableEq α]

def deq (x y : rbnode α) : Decidable (Eq x y) := match x, y with
  | .lf, .lf => isTrue rfl
  | .lf, .node _ _ _ _ => isFalse (by intro h; cases h)
  | .node _ _ _ _, .lf => isFalse (by intro h; cases h)
  | .node c1 d1 l1 r1, .node c2 d2 l2 r2 =>
    if h₁ : c1 = c2 then
      if h₂ : d1 = d2 then
        match deq l1 l2, deq r1 r2 with
        | isTrue h₃, isTrue h₄ => isTrue (by rw [h₁, h₂, h₃, h₄])
        | isFalse h₃, _ => isFalse (by intro h; cases h; contradiction)
        | _, isFalse h₄ => isFalse (by intro h; cases h; contradiction)
      else isFalse (by intro h; cases h; contradiction)
    else isFalse (by intro h; cases h; contradiction)

instance : DecidableEq (rbnode α) := deq

def mem (x : α) : rbnode α → Bool
  | .lf => False
  | .node _ v l r => match o.compare v x with
    | .lt => l.mem x
    | .eq => true
    | .gt => r.mem x

def balance : Colour → α → rbnode α → rbnode α → rbnode α
  | .black, vr, .node .red y (.node .red vl ll lr) rl, rr
  | .black, vr, (.node .red vl ll (.node .red y lr rl)), rr
  | .black, vl, ll, (.node .red vr (.node .red y lr rl) rr)
  | .black, vl, ll, (.node .red y lr (.node .red vr rl rr)) =>
    .node .red y (.node .black vl ll lr) (.node .black vr rl rr)

  | c, v, l, r => .node c v l r

def black : rbnode α → Prop
  | .lf | .node .black _ _ _ => true
  | .node .red _ _ _ => false

def keySet : rbnode α → Finset α
  | .node _ v l r => (keySet l) ∪ {v} ∪ (keySet r)
  | .lf => {}

def nodes : rbnode α → Finset (rbnode α)
  | x@(node _ _ l r) => (nodes l) ∪ {x} ∪ (nodes r)
  | .lf => {.lf}

def redInv : rbnode α → Prop
  | .node .red _ (.node .black _ _ _) (.node .black _ _ _) => true
  | _ => false

def bstInv : rbnode α → Prop
  | .node _ v l r => ∀ a ∈ l.keySet, ∀ b ∈ r.keySet, a < v ∧ v < b
  | .lf => true


def blacken : rbnode α → rbnode α
  | .node _ v l r => .node .black v l r
  | .lf => .lf

def insert (x : α) : rbnode α → rbnode α := blacken ∘ ins
  where ins : rbnode α → rbnode α
    | .lf => .node .red x .lf .lf
    | z@(node col y l r) => match o.compare x y with
      | .lt => balance col y (ins l) r
      | .eq => z
      | .gt => balance col y l (ins r)

end rbnode

