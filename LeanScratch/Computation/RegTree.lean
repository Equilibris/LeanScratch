import LeanScratch.Vec
import LeanScratch.Fin2

namespace Comp

inductive RegTree
  | lf (n : Nat)
  | br (l r : RegTree)

abbrev RegTree.toStore : RegTree → Type
  | .lf n => Vec Nat n
  | .br l r => l.toStore × r.toStore

def Vec.zero {n} : Vec Nat n :=
  match n with
  | 0 => %[]
  | _+1 => 0 %::zero

def RegTree.toStore.zero {r : RegTree} : r.toStore :=
  match r with
  | .lf _ => Vec.zero
  | .br _ _ => ⟨zero, zero⟩

instance {r : RegTree} : Repr r.toStore where
  reprPrec v _ := f v
    where
      f {r : RegTree} (v : r.toStore) : Std.Format := match r with
      | .lf _ => repr v
      | .br _ _ => .bracket "⟨" (f v.fst ++ ", " ++ f v.snd) "⟩"

abbrev RegTree.toIdx : RegTree → Type
  | .lf n => Fin2 n
  | .br l r => l.toIdx ⊕ r.toIdx
