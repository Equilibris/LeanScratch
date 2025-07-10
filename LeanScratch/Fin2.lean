import Mathlib.Data.Fin.Fin2
import Mathlib.Util.WhatsNew
import LeanScratch.Fintype2

deriving instance Repr for Fin2
deriving instance DecidableEq for Fin2

def List.getFin2 : (l : List α) → Fin2 l.length → α
  | hd :: _, .fz => hd
  | _ :: tl, .fs x => tl.getFin2 x

namespace Fin2

instance decEq : DecidableEq (Fin2 n) := fun
  | .fz, .fs _ | .fs _, .fz => .isFalse Fin2.noConfusion
  | .fz, .fz => .isTrue rfl
  | .fs a, .fs b => match decEq a b with
    | .isTrue p => .isTrue $ p.rec rfl
    | .isFalse p => .isFalse (p ∘ (Fin2.fs.injEq _ _).mp)

instance instFintype2 : Fintype2 (Fin2 n) := match n with
  | 0 => ⟨[], (fun x => by cases x), .nil⟩
  | n+1 =>
    let ⟨els, p, nodup⟩ := instFintype2 (n := n)
    ⟨.fz :: (.map .fs els), fun
      | .fz => List.mem_cons_self _ _
      | .fs s => by simp [p],
      .cons (by simp) $ List.Nodup.map (@fs.inj _) nodup⟩

instance {v : Fin n} : Fin2.IsLT (v.val) n := ⟨v.isLt⟩

def ofFin (fin : Fin n) : Fin2 n := Fin2.ofNat' fin.val

inductive Le : {n : Nat} → Fin2 n → Fin2 n → Prop
  | rfl : Le .fz .fz
  | fz : Le .fz (.fs v)
  | fs : Le a b → Le (.fs a) (.fs a)
inductive Lt : {n : Nat} → Fin2 n → Fin2 n → Prop
  | fz : Lt .fz (.fs v)
  | fs : Lt a b → Lt (.fs a) (.fs a)

instance : LE (Fin2 n) := ⟨Le⟩
instance : LT (Fin2 n) := ⟨Lt⟩

instance : Bot (Fin2 (n+1)) where
  bot := .fz

def bot_le : {n : Fin2 (n + 1)} → ⊥ ≤ n | .fz => .rfl | .fs _ => .fz

instance : OrderBot (Fin2 (n+1)) where
  bot_le _ := bot_le

def LE.refl : ∀ (x : Fin2 n), x ≤ x
  | .fz => .rfl
  | .fs v => .fs $ refl v

def LE.trans : {a b c : Fin2 n} → a ≤ b → b ≤ c → a ≤ c
  | _,_,_, .rfl, x => x
  | _,_,_, .fs ha, b => sorry
  | _,_,_, .fz, .fs b => bot_le

instance : PartialOrder (Fin2 n) where
  lt := instLT_leanScratch.lt
  lt_iff_le_not_le := sorry
  le_refl := LE.refl
  le_trans := sorry
  le_antisymm := sorry

