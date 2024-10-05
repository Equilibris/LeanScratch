import LeanScratch.Semantics.STLC.StrongNorm.CTySpec
import LeanScratch.Semantics.STLC.StrongNorm.ArgCount

namespace STLC

inductive TyArr : List Ty → Type
  | nil : TyArr []
  | cons (h : ArgCount hd) (t : TyArr tl) : TyArr (hd :: tl)

namespace TyArr

def concat : TyArr a → TyArr b → TyArr (a ++ b)
  | .nil, a => a
  | .cons hd tl, v => .cons hd (concat tl v)

instance : HAppend (TyArr a) (TyArr b) (TyArr (a ++ b)) := ⟨TyArr.concat⟩
theorem cons_append {a : TyArr A} {b : TyArr B} : .cons z (a ++ b) = (TyArr.cons z a) ++ b := rfl

@[simp]
theorem nil_concat {Γ' : TyArr Γ} : (TyArr.nil ++ Γ') = Γ' := rfl

def get
    {idx : ℕ} (h : Γ[idx]? = some ty) (v : TyArr Γ)
    : ArgCount ty := match Γ, idx with
  | [], _ => Option.noConfusion (List.getElem?_nil.symm.trans h)
  | hd :: tl, 0 =>
    let h := (Option.some.injEq _ _).mp $ List.getElem?_cons_zero.symm.trans h
    match v with
    | .cons hd _ => cast (by rw [←h]) hd
  | hd :: tl, n+1 =>
    match v with
    | cons _ tl' => get (List.getElem?_cons_succ.symm.trans h) tl'

theorem get_append_assoc
    {Γ₁' : TyArr Γ₁} {Γ₂' : TyArr Γ₂} {Γ₃' : TyArr Γ₃}
    {h  : (Γ₁ ++  Γ₂ ++ Γ₃ )[idx]? = some v}
    (h' : (Γ₁ ++ (Γ₂ ++ Γ₃))[idx]? = some v)
    : get h (Γ₁' ++  Γ₂' ++ Γ₃') = get h' (Γ₁' ++ (Γ₂' ++ Γ₃')) :=
  match Γ₁, Γ₁', idx with
  | [], .nil, _ => rfl
  | hd :: tl, .cons hd' tl', 0 => by
    change get h (cons hd' (tl' ++ Γ₂' ++ Γ₃')) = get h' (cons hd' (tl' ++ (Γ₂' ++ Γ₃')))
    dsimp [get]
  | hd :: tl, .cons hd' tl', n+1 => by
    change get h (cons hd' (tl' ++ Γ₂' ++ Γ₃')) = get h' (cons hd' (tl' ++ (Γ₂' ++ Γ₃')))
    dsimp [get]
    exact get_append_assoc _

theorem get_append
    {Γ₁' : TyArr Γ₁} {Γ₂' : TyArr Γ₂}
    {h  : (Γ₁ ++ Γ₂)[idx]? = some t}
    (h' :         Γ₁[idx]? = some t)
    : get h (Γ₁' ++ Γ₂') = get h' Γ₁' :=
  match Γ₁, Γ₁', idx with
  | [], _, _ => (Nat.not_succ_le_zero _ (List.getElem?_lt_length h')).elim
  | hd :: tl, .cons hd' tl', 0 => by
    change (hd :: (tl ++ Γ₂))[0]? = _ at h
    change get _ (TyArr.cons hd' (tl' ++ Γ₂')) = _
    dsimp [get]
  | hd :: tl, .cons hd' tl', n+1 => by
    change (hd :: (tl ++ Γ₂))[n + 1]? = _ at h
    change get _ (TyArr.cons hd' (tl' ++ Γ₂')) = _
    dsimp [get]
    exact get_append _

theorem get_idx_eq_jdx
    {idx jdx : ℕ}
    {Γ' : TyArr Γ}
    {h  : Γ[idx]? = some t}
    (h' : Γ[jdx]? = some t)
    (heq : idx = jdx)
    : get h Γ' = get h' Γ' :=
  match Γ, Γ', idx, jdx with
  | [], .nil, _, _ => Option.noConfusion (List.getElem?_nil.symm.trans h)
  | hd :: tl, .cons hd' tl', 0, 0 => rfl
  | hd :: tl, .cons hd' tl', idx+1, jdx+1 => by
    dsimp [get]
    simp only [add_left_inj] at heq
    exact get_idx_eq_jdx _ heq

theorem get_append_right
    {Γ₁' : TyArr Γ₁} {Γ₂' : TyArr Γ₂}
    {h  : (Γ₁ ++ Γ₂)[idx]? = some t}
    (hLe : Γ₁.length ≤ idx)
    (h' :  Γ₂[idx - Γ₁.length]? = some t)
    : get h (Γ₁' ++ Γ₂') = get h' Γ₂' :=
  match Γ₁, Γ₁', idx with
  | [], .nil, idx => by
    change get _ Γ₂' = _
    dsimp [List.length_nil, Nat.sub_zero] at h h'
    rfl
  | hd :: tl, .cons hd' tl', 0 => by
    simp only [nonpos_iff_eq_zero, List.length_eq_zero, one_ne_zero] at hLe
  /- | hd :: tl, .cons hd' tl', [], .nil,  n+1 => by -/
  /-   simp only [List.length_cons, Nat.reduceSubDiff, List.getElem?_nil] at h' -/
  | hd :: tl, .cons hd' tl', n+1 => by
    change (hd :: (tl ++ _))[n + 1]? = _ at h
    change get _ (TyArr.cons hd' (tl' ++ Γ₂')) = _
    dsimp [get]
    simp only [List.length_cons, add_le_add_iff_right] at hLe
    dsimp at h'
    have : (n + 1 - (tl.length + 1)) = (n - tl.length) := Nat.add_sub_add_right n 1 tl.length
    rw [this] at h'
    rw [get_idx_eq_jdx h' this]
    exact get_append_right hLe _

inductive Every (p : ∀ {s}, ArgCount s → Prop) : TyArr Γ → Prop
  | nil : Every p .nil
  | cons (hd : p h) : Every p t → Every p (TyArr.cons h t)
  -- | cons (hd : p h) (tl : Every p t) : Every p (TyArr.cons h t) -- for unknown reasons the line below breaks things
  -- TODO: bug report

theorem Every_get
    {Γ' : TyArr Γ} (h : Every p Γ')
    {hGet : Γ[idx]? = some val}
    : p (TyArr.get hGet Γ') :=
  match Γ, Γ', idx, h with
  | [], .nil, _, _ => Option.noConfusion (List.getElem?_nil.symm.trans hGet)
  | h :: t, .cons hd tl, 0, .cons hhd _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hGet
    subst hGet
    simp only [get, cast_eq]
    exact hhd
  | h :: t, .cons _ tl, n+1, .cons _ htl => Every_get htl

