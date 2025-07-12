
def Subsingleton.neg (t : Type _) : Type _ := (v : t) → Empty

instance : Subsingleton (Subsingleton.neg t) where
  allEq a b := funext λ i ↦ Subsingleton.allEq (a i) (b i)

