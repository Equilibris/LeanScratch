import LeanScratch.Semantics.STLC.StrongNorm.CTySpec
import LeanScratch.Semantics.STLC.StrongNorm.ArgCount
import LeanScratch.Semantics.STLC.StrongNorm.TyArr

namespace STLC

open ArgCount in
def upperBoundRed
    {x : Stx} (hTy : CTySpec Γ x ty)
    (v : TyArr Γ) : ArgCount ty :=
  match x, hTy with
  | .bvar _, .bvar hTy => TyArr.get hTy v
  | .abs _ _, .abs hTy => fun z => upperBoundRed hTy $ .cons z v
  | .app _ _, .app ha hb =>
    let ha := upperBoundRed ha v
    let hb := upperBoundRed hb v
    addN (ha hb) (naturalize hb).succ

open ArgCount in
theorem upperBoundRed_eq_replace.bvarShift
    {repl : Stx} {t' : Ty}
    {Γ' : TyArr Γ} {Γ'₂ : TyArr Γ₂}  {Γ'₃ : TyArr Γ₃}
    (pRepl : CTySpec (Γ₃ ++ Γ) repl t')
    (hRepl : CTySpec (Γ₃ ++ Γ₂ ++ Γ) (Stx.bvarShift Γ₂.length Γ₃.length repl) t')
    : upperBoundRed pRepl (Γ'₃ ++ Γ') = upperBoundRed hRepl (Γ'₃ ++ Γ'₂ ++ Γ') :=
  match repl with
  | .bvar idx => by
    dsimp [Stx.bvarShift] at hRepl
    cases pRepl; cases hRepl; next pRepl hRepl =>
    dsimp [upperBoundRed]
    split at hRepl
    <;> rename_i hRepl' h
    · have : (if idx < Γ₃.length then idx else idx + Γ₂.length) = idx := by simp only [h, ↓reduceIte]
      rw [TyArr.get_idx_eq_jdx hRepl this]
      clear *-h
      rw [List.append_assoc _ _ _] at hRepl
      rw [TyArr.get_append_assoc hRepl]
      rw [List.getElem?_append h] at pRepl hRepl
      rw [TyArr.get_append hRepl, TyArr.get_append hRepl]
    · have : (if idx < Γ₃.length then idx else idx + Γ₂.length) = idx + Γ₂.length := by simp only [h, ↓reduceIte]
      rw [TyArr.get_idx_eq_jdx hRepl this]
      clear *-h
      rw [not_lt] at h

      rw [List.append_assoc _ _ _] at hRepl
      rw [TyArr.get_append_assoc hRepl]
      rw [List.getElem?_append_right h] at pRepl
      have := h.trans (Nat.le_add_right idx Γ₂.length)
      rw [List.getElem?_append_right this] at hRepl
      rw [TyArr.get_append_right this hRepl, TyArr.get_append_right h pRepl]
      clear *-h
      have : idx + Γ₂.length - Γ₃.length = idx - Γ₃.length + Γ₂.length := Nat.sub_add_comm h
      rw [this] at hRepl
      rw [TyArr.get_idx_eq_jdx hRepl this]
      rw [List.getElem?_append_right (Nat.le_add_left Γ₂.length (idx - Γ₃.length))] at hRepl
      rw [TyArr.get_append_right (Nat.le_add_left Γ₂.length (idx - Γ₃.length)) hRepl]
      have : idx - Γ₃.length + Γ₂.length - Γ₂.length = idx - Γ₃.length := Nat.add_sub_self_right (idx - Γ₃.length) Γ₂.length
      rw [this] at hRepl
      rw [TyArr.get_idx_eq_jdx hRepl this]
  | .abs ty body => by
    dsimp [Stx.bvarShift] at hRepl
    cases pRepl; cases hRepl; next pArg hBody =>
    dsimp [upperBoundRed]
    funext z
    change CTySpec ((ty :: Γ₃) ++ Γ) _ _ at pArg
    change CTySpec ((ty :: Γ₃) ++ Γ₂ ++ Γ) _ _ at hBody
    change upperBoundRed _ ((TyArr.cons z Γ'₃) ++ Γ')
      = upperBoundRed _ ((TyArr.cons z Γ'₃) ++ Γ'₂ ++ Γ')
    exact upperBoundRed_eq_replace.bvarShift pArg hBody
  | .app a b => by
    dsimp [Stx.bvarShift] at hRepl
    cases pRepl; cases hRepl; next hap hbp _ har hbr =>
    obtain rfl := TySpec_unique (bvarShift_maintain_gen (CTySpec_TySpec hap)) (CTySpec_TySpec har)
    dsimp [upperBoundRed]
    rw [upperBoundRed_eq_replace.bvarShift hap har, upperBoundRed_eq_replace.bvarShift hbp hbr]

open ArgCount in
theorem upperBoundRed_eq_replace.bvar {Γ₂ Γ : List Ty} {repl : Stx} {t' : Ty} {Γ' : TyArr Γ} {replSz : ArgCount t'} {t : Ty}
    {Γ'₂ : TyArr Γ₂} (pRepl : CTySpec Γ repl t') (z : upperBoundRed pRepl Γ' = replSz) (idx : ℕ)
    (h : CTySpec (Γ₂ ++ t' :: Γ) (Stx.bvar idx) t)
    (hRepl :
      CTySpec (Γ₂ ++ Γ)
        (match compare idx Γ₂.length with
        | Ordering.lt => Stx.bvar idx
        | Ordering.eq => Stx.bvarShift Γ₂.length 0 repl
        | Ordering.gt => Stx.bvar (idx - 1))
        t) :
    upperBoundRed h (Γ'₂ ++ TyArr.cons replSz Γ') = upperBoundRed hRepl (Γ'₂ ++ Γ') := by
  split at hRepl
  <;> dsimp only at hRepl
  <;> rename_i hOrd
  <;> simp only [Nat.compare_eq_eq, Nat.compare_eq_lt, Nat.compare_eq_gt] at hOrd
  case h_1 => 
    cases h; cases hRepl; next h hRepl =>
    dsimp [upperBoundRed]
    have : Γ₂[idx]? = some t := by rw [←hRepl, List.getElem?_append hOrd]
    rw [TyArr.get_append this, TyArr.get_append this]
  case h_3 =>
    cases h; cases hRepl; next h hRepl =>
    dsimp [upperBoundRed]
    have : Γ₂.length ≤ idx := Nat.le_of_succ_le hOrd
    rw [List.getElem?_append_right this] at h
    rw [TyArr.get_append_right this h]
    have : Γ₂.length ≤ idx - 1 := Nat.le_sub_one_of_lt hOrd
    rw [List.getElem?_append_right this] at hRepl
    rw [TyArr.get_append_right this hRepl]
    change ([t'] ++ Γ)[_]? = _ at h
    change TyArr.get h ((TyArr.cons replSz .nil) ++ Γ') = _
    clear *-hOrd z
    have : [t'].length ≤ idx - Γ₂.length := Nat.le_sub_of_add_le' hOrd
    rw [List.getElem?_append_right this] at h
    rw [TyArr.get_append_right this h]
    have : idx - Γ₂.length - [t'].length = idx - 1 - Γ₂.length := by
      dsimp only [List.length_singleton]
      rw [Nat.sub_right_comm]
    rw [this] at h
    rw [TyArr.get_idx_eq_jdx h this]
  · cases h; next h =>
    subst hOrd
    dsimp [upperBoundRed]
    rw [List.getElem?_append_right (le_refl _)] at h
    rw [TyArr.get_append_right (le_refl _) h]
    have : Γ₂.length - Γ₂.length = 0 := Nat.sub_self Γ₂.length
    rw [this] at h
    rw [TyArr.get_idx_eq_jdx h this]
    simp only [List.getElem?_cons_zero, Option.some_inj] at h
    subst h
    simp only [TyArr.get, cast_eq]
    rw [←z]
    clear *-
    change CTySpec ([] ++ Γ) _ _ at pRepl
    change CTySpec ([] ++ Γ₂ ++ Γ) (Stx.bvarShift _ ([] : List Ty).length _) _ at hRepl
    change upperBoundRed _ (TyArr.nil ++ Γ') = upperBoundRed _ (TyArr.nil ++ Γ'₂ ++ Γ')
    exact upperBoundRed_eq_replace.bvarShift pRepl hRepl

open ArgCount in
theorem upperBoundRed_eq_replace
    {Γ'₂ : TyArr Γ₂}
    (pRepl : CTySpec Γ repl t')
    (z : upperBoundRed pRepl Γ' = replSz)
    (h : CTySpec (Γ₂ ++ (t' :: Γ)) s t)
    (hRepl : CTySpec (Γ₂ ++ Γ) (Stx.replace (Γ₂.length) s repl) t)
    : upperBoundRed h (Γ'₂ ++ (TyArr.cons replSz Γ')) = upperBoundRed hRepl (Γ'₂ ++ Γ') :=
  match s with
  -- For some reason I need to extract this into its own function.
  -- Unknown why
  | .bvar idx => upperBoundRed_eq_replace.bvar pRepl z idx h hRepl
  | .abs ty body => by
    dsimp [Stx.replace] at hRepl
    cases h; cases hRepl; next h hRepl =>
    dsimp [upperBoundRed]
    apply funext
    intro x
    rw [TyArr.cons_append]
    dsimp [←List.cons_append] at h hRepl
    exact upperBoundRed_eq_replace pRepl z h hRepl
  | .app a b => by
    cases h; cases hRepl; next hb ha _ hbRepl haRepl =>
    simp only [upperBoundRed]
    obtain rfl := ((Ty.arr.injEq _ _ _ _).mp
      $ TySpec_unique
      (CTySpec_TySpec haRepl)
      (TySpec_replace_gen (x := t') (CTySpec_TySpec pRepl) (CTySpec_TySpec ha))).1
    rw [upperBoundRed_eq_replace pRepl z ha haRepl,
        upperBoundRed_eq_replace pRepl z hb hbRepl]

/-- info: 'STLC.upperBoundRed_eq_replace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms upperBoundRed_eq_replace
