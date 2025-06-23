namespace DenSem

class Den (A : Type _) where
  obj : Type _
  denote : A → obj

def denote {A : Type _} [inst : Den A] (x : A) : inst.obj :=
  inst.denote x

notation "⟦" t "⟧"  => denote t

