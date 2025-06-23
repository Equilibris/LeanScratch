import LeanScratch.Semantics.DenSem.Denotation

namespace DenSem.Imp

mutual
inductive A (L : Type) where
  | l (n : Int)
  | add (a b : A L)
  | loc (l : L)

inductive B (L : Type) where
  | tt
  | ff
  | eq (a b : A L)
  | neg (v : B L)
end

/-- wh is a subsingleton -/
inductive C (L : Type) (wh : Type) where
  | skip
  | ass (l : L) (ex : A L)
  | seq (a b : C L wh)
  | eif (b : B L) (t f : C L wh)
  | ewhile (en : wh) (c : B L) (body : C L wh)

mutual
def A.denote : A L → (L → Int) → Int
    | .l n, _ => n
    | .loc lo, z => z lo
    | .add a b, x => A.denote a x + A.denote b x

def B.denote : B L → (L → Int) → Bool
    | .tt, _ => .true
    | .ff, _ => .false
    | .eq a b, x => A.denote a x == A.denote b x
    | .neg b, x => !B.denote b x
end

instance : Den (A L) where
  obj := (L → Int) → Int
  denote := A.denote

