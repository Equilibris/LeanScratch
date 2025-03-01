import LeanScratch.Vec
import LeanScratch.Fin2

namespace Comp

inductive RegTree
  | lf (n : Nat)
  | br (l r : RegTree)

def Vec.zero {n} : Vec Nat n :=
  match n with
  | 0 => %[]
  | _+1 => 0 %::zero

namespace RegTree

abbrev toStore : RegTree → Type
  | .lf n => Vec Nat n
  | .br l r => l.toStore × r.toStore

def toStore.zero {r : RegTree} : r.toStore :=
  match r with
  | .lf _ => Vec.zero
  | .br _ _ => ⟨zero, zero⟩

instance {r : RegTree} : Repr r.toStore where
  reprPrec v _ := f v
    where
      f {r : RegTree} (v : r.toStore) : Std.Format := match r with
      | .lf _ => repr v
      | .br _ _ => .bracket "⟨" (f v.fst ++ ", " ++ f v.snd) "⟩"

abbrev toIdx : RegTree → Type
  | .lf n => Fin2 n
  | .br l r => l.toIdx ⊕ r.toIdx

instance instDecEq {r : RegTree} : DecidableEq r.toIdx := match r with
  | .lf n => Fin2.decEq
  | .br l r => fun
    | .inl a, .inl b
    | .inr a, .inr b =>
      match instDecEq a b with
      | .isTrue  p => .isTrue $ p.rec rfl
      | .isFalse p => .isFalse fun x => by
        injections x
        exact p x
    | .inl _, .inr _ | .inr _, .inl _ => .isFalse Sum.noConfusion

instance instFintype2 {r : RegTree} : Fintype2 (r.toIdx) := match r with
  | .lf n => Fin2.instFintype2
  | .br l r => {
    elems :=
      (instFintype2 (r := l)).elems.map Sum.inl ++
      (instFintype2 (r := r)).elems.map Sum.inr
    complete := fun | .inl _ | .inr _ => by simp [instFintype2.complete]
    nodup :=
      List.nodup_append.mpr ⟨
        List.Nodup.map (@Sum.inl.inj _ _) instFintype2.nodup,
        List.Nodup.map (@Sum.inr.inj _ _) instFintype2.nodup,
        by simp [List.Disjoint]⟩
  }
  /- elems := match r with -/
  /-   | .lf n => (Fin2.instFintype n).elems -/
  /-   | .br l r => sorry -/
  /- complete := sorry -/

abbrev lookup (r : RegTree) (store : r.toStore) (idx : r.toIdx) : Nat :=
  match r with
  | .lf _ => store.lookup idx
  | .br _ _ =>
    match idx with
    | .inl idx => RegTree.lookup _ store.fst idx
    | .inr idx => RegTree.lookup _ store.snd idx

def set (r : RegTree) (store : r.toStore) (idx : r.toIdx) (v : Nat) : r.toStore :=
  match r, idx, store with
  | .lf _, idx, s => s.set idx v
  | .br l _, .inl idx, ⟨sl, sr⟩ => ⟨l.set sl idx v, sr⟩
  | .br _ r, .inr idx, ⟨sl, sr⟩ => ⟨sl, r.set sr idx v⟩

theorem set.overwrite {r : RegTree} {store : r.toStore} {idx : r.toIdx}
    : r.set (r.set store idx y) idx x = r.set store idx x :=
  match r, idx with
  | .lf _, idx => Vec.set.overwrite
  | .br _ _, .inr _
  | .br _ _, .inl _ => by
    dsimp [set]
    rw [set.overwrite]

theorem set.comm_ne {r : RegTree} {idx jdx : r.toIdx} {s1 : r.toStore} (hNe : idx ≠ jdx)
    : r.set (r.set s1 idx x) jdx y = r.set (r.set s1 jdx y) idx x :=
  match r, idx, jdx with
  | .lf _, idx, jdx => Vec.set.comm_ne hNe
  | .br _ _, .inl x, .inr y | .br _ _, .inr x, .inl y => rfl
  | .br l r, .inl x, .inl y | .br l r, .inr x, .inr y => by
    dsimp [set]
    rw [RegTree.set.comm_ne]
    exact hNe ∘ (·.rec rfl)

def set_many (r : RegTree) (store : r.toStore) : List (r.toIdx × Nat) → r.toStore
  | [] => store
  | ⟨idx, x⟩ :: tl => r.set (r.set_many store tl) idx x

def set_many.stalin [DecidableEq T] : List (T × V) → List (T × V)
  | [] => []
  | ⟨k, v⟩ :: tl => ⟨k, v⟩ :: ((set_many.stalin tl).filter $ (· ≠ k) ∘ Prod.fst)

-- Closer to the one-child policy (what happend to monday) than stalin
theorem set_many.stalin.nodup
    [DecidableEq T] {ls : List (T × V)}
    : (set_many.stalin ls).map Prod.fst |>.Nodup :=
  match ls with
  | [] => .nil
  | hd :: tl => .cons
    (by simp [←List.filter_map, List.mem_filter])
    (by simp [←List.filter_map, List.Nodup.filter, nodup])

theorem set_many.stalin.lem {r : RegTree} {s : r.toStore} (k : r.toIdx) (v : ℕ)
    (sub : List (r.toIdx × ℕ))
    : r.set (r.set_many s (List.filter ((fun x ↦ decide ¬x = k) ∘ Prod.fst) sub)) k v =
      r.set (r.set_many s sub) k v := by
  induction sub
  · rfl
  case cons hd tl ih =>
    rcases hd with ⟨hk, hv⟩
    rw [List.filter_cons]
    split <;> rename_i h <;> simp at h <;> dsimp [set_many]
    · rw [RegTree.set.comm_ne h, RegTree.set.comm_ne h, ih]
    · rw [h, RegTree.set.overwrite, ih]

theorem set_many.stalin.sm
    {r : RegTree} {s : r.toStore}
    (ls : List (r.toIdx × Nat))
    : r.set_many s ls = r.set_many s (stalin ls) :=
  match ls with
  | [] => rfl
  | ⟨k, v⟩ :: tl => by dsimp [set_many, stalin]; rw [lem, sm]

/- theorem set_many.stalin.nochange -/
/-     {ls : List (T × U)} -/
/-     [DecidableEq T] -/
/-     {} -/
/-     : set_many.stalin ls = ls := -/
/-   sorry -/

theorem set_many.comp {r : RegTree} {base : r.toStore} {l₁ l₂ : List (r.toIdx × Nat)} :
    r.set_many (r.set_many base l₁) l₂ = r.set_many base (l₂ ++ l₁) :=
  match l₂ with
  | [] => rfl
  | ⟨idx, v⟩ :: tl => by
    dsimp [set_many]
    rw [set_many.comp]

def set_many.perm {r : RegTree} {l₁ l₂ : List (r.toIdx × Nat)}
    {s : r.toStore}
    (hNoDup : l₁.map Prod.fst |>.Nodup)
    (hPerm : List.Perm l₁ l₂)
    : r.set_many s l₁ = r.set_many s l₂ := by
  induction hPerm generalizing s
  case cons el _ ih =>
    rename_i tl₁ _
    rcases hNoDup with (_|⟨hhd, hNoDup⟩)
    simp only [set_many]
    rw [ih hNoDup]
  case swap x y ls =>
    rcases x with ⟨xk, xv⟩
    rcases y with ⟨yk, yv⟩
    rcases hNoDup with (_|⟨hhd, hnodup⟩)
    simp only [List.map_cons, List.mem_cons, List.mem_map, Prod.exists, exists_and_right,
      exists_eq_right, ne_eq, forall_eq_or_imp, forall_exists_index] at hhd
    rcases hhd with ⟨neq, _⟩
    dsimp [set_many]
    rw [set.comm_ne neq]
  case trans a _ iha ihb =>
    calc
      _ = _ := iha hNoDup
      _ = _ := ihb $ (List.Perm.nodup_iff $ List.Perm.map _ a).mp hNoDup
  case nil => rfl

@[ext]
def store.ext {r : RegTree} {s1 s2 : r.toStore}
    (h : r.lookup s1 = r.lookup s2)
    : s1 = s2 :=
  match r, s1, s2 with
  | .lf _, s1, s2 => Vec.ext h
  | .br l r, ⟨l₁, r₁⟩, ⟨l₂, r₂⟩ => by
    have := Function.funext_iff.mp h
    have l : l.lookup l₁ = l.lookup l₂ := funext $ λ x ↦ this (.inl x)
    have r : r.lookup r₁ = r.lookup r₂ := funext $ λ x ↦ this (.inr x)
    rw [RegTree.store.ext l, RegTree.store.ext r]

end RegTree

