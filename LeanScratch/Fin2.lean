import Mathlib.Data.Fin.Fin2
import Mathlib.Util.WhatsNew
import LeanScratch.Fintype2

instance Fin2.decEq : DecidableEq (Fin2 n) := fun
  | .fz, .fs _ | .fs _, .fz => .isFalse Fin2.noConfusion
  | .fz, .fz => .isTrue rfl
  | .fs a, .fs b => match decEq a b with
    | .isTrue p => .isTrue $ p.rec rfl
    | .isFalse p => .isFalse (p ∘ (Fin2.fs.injEq _ _).mp)

instance Fin2.instFintype2 : Fintype2 (Fin2 n) := match n with
  | 0 => ⟨[], (fun x => by cases x), .nil⟩
  | n+1 =>
    let ⟨els, p, nodup⟩ := instFintype2 (n := n)
    ⟨.fz :: (.map .fs els), fun
      | .fz => List.mem_cons_self _ _
      | .fs s => by simp [p],
      .cons (by simp) $ List.Nodup.map (@fs.inj _) nodup⟩

instance {v : Fin n} : Fin2.IsLT (v.val) n := ⟨v.isLt⟩

def Fin2.ofFin (fin : Fin n) : Fin2 n := Fin2.ofNat' fin.val
