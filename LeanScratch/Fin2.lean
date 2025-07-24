import Mathlib.Data.Fin.Fin2
import Mathlib.Util.WhatsNew
import LeanScratch.Fintype2

deriving instance Repr for Fin2
deriving instance DecidableEq for Fin2

def List.getFin2 : (l : List α) → Fin2 l.length → α
  | hd :: _, .fz => hd
  | _ :: tl, .fs x => tl.getFin2 x

namespace Fin2
def getFin2_mem : {l : List α} → (idx : Fin2 l.length) → l.getFin2 idx ∈ l
  | _ :: _, .fz => .head _
  | h :: _, .fs idx => .tail h $ idx.getFin2_mem

def ofMem : {l : List α} → x ∈ l → ∃ v, x = l.getFin2 v
  | [], h => False.elim $ (List.mem_nil_iff _).mp h
  | _ :: _, .head _ => ⟨.fz, rfl⟩
  | _ :: _, .tail _ h =>
    have ⟨v, x⟩ := Fin2.ofMem h
    ⟨.fs v, x⟩

/- def x : {l : List α} → Fin2 l.length → l.get -/

def toNat_eq : {n : Nat} → {a b : Fin2 n} → a.toNat = b.toNat → a = b
  | _+1, .fs _, .fs _, heq => 
    congr rfl $ toNat_eq $ (Nat.succ.injEq _ _).mp heq
  | _+1, .fz, .fz, _ => rfl

def toNat_lt : {n : Nat} → {f : Fin2 n} → f.toNat < n
  | _+1, .fs _ => Nat.succ_le_succ $ toNat_lt
  | _+1, .fz => Nat.zero_lt_succ _

def get?_toNat : {ls : List α} → {idx : Fin2 ls.length} → ls.get? idx.toNat = .some (ls.getFin2 idx)
  | _ :: _, .fz => rfl
  | _ :: _, .fs idx => get?_toNat (idx := idx)

def getFin2_Nodup_Injective {ls : List α} (nd : ls.Nodup) : Function.Injective $ ls.getFin2 := fun a b heq => by
  cases h : compare a.toNat b.toNat
  <;> simp only [Nat.compare_eq_lt, Nat.compare_eq_gt, Nat.compare_eq_eq] at h
  any_goals have := List.nodup_iff_get?_ne_get?.mp nd _ _ h toNat_lt
  any_goals rw [get?_toNat, get?_toNat] at this
  · exact False.elim (this (congrArg some heq))
  · exact toNat_eq h
  · exact False.elim (this (congrArg some heq.symm))

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

def Le {n : Nat} (a b : Fin2 n) : Prop :=
  a.toNat ≤ b.toNat

instance : LE (Fin2 n) := ⟨Le⟩

instance : Bot (Fin2 (n+1)) where
  bot := .fz

instance : OrderBot (Fin2 (n+1)) where
  bot_le _ := Nat.zero_le _

instance : PartialOrder (Fin2 n) where
  le_refl _ := Nat.le_refl _
  le_trans _ _ _ := Nat.le_trans
  le_antisymm a b ha hb := toNat_eq $ Nat.le_antisymm ha hb

def extend {c : List α} : {a b : List α} → Fin2 (a ++ c).length → Fin2 (a ++ b ++ c).length
  | [], [], x => x
  | [], _ :: tb, v => .fs $ extend v
  | _ :: ta, b, .fz => .fz
  | _ :: ta, b, .fs v => .fs $ extend v

theorem extend.eq {c : List α}
    : {a b : List α}
    → {i : Fin2 (a ++ c).length}
    → (a ++ c).getFin2 i = (a ++ b ++ c).getFin2 (@extend _ c a b i) := by
  intro a b i
  induction a, b, i using extend.induct
  <;> unfold extend
  any_goals rfl
  all_goals assumption


