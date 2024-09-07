import LeanScratch.Semantics.STLC.Stx
import LeanScratch.Semantics.STLC.Red
import Mathlib.Data.Rel
import LeanScratch.Relation

namespace STLC

inductive TySpec : List Ty → Stx → Ty → Prop
  | fvar : TySpec _ (.fvar ty) ty
  | bvar : Γ[idx]? = some ty → TySpec Γ (.bvar idx) ty

  | app : TySpec Γ fn (argTy ⇒ retTy) → TySpec Γ arg argTy
      → TySpec Γ (.app fn arg) retTy
  | abs : TySpec (ty :: Γ) body retTy
      → TySpec Γ (.abs ty body) (ty ⇒ retTy)

theorem TyUnique : TySpec Γ i o₁ → TySpec Γ i o₂ → o₁ = o₂ := by
  intro a b
  induction i generalizing Γ o₁ o₂
  · cases a
    next ha =>
    cases b
    next hb =>
    exact (Option.some.injEq _ _).mp $ ha.symm.trans hb
  · cases a
    cases b
    rfl
  case app fn_ih _ =>
    cases a
    next a argTy₁ fnTy₁ =>
    cases b
    next b argTy₂ fnTy₂ =>
    exact ((Ty.arr.injEq _ _ _ _).mp $ fn_ih fnTy₁ fnTy₂).2

  case abs body_ih =>
    cases a
    next a ty₁ =>
    cases b
    next b ty₂ =>
    exact (Ty.arr.injEq _ _ _ _).mpr ⟨rfl, body_ih ty₁ ty₂⟩

/- theorem ReplacePreserve : Γ[n]? = some replTy → TySpec Γ repl replTy → TySpec Γ v ty → TySpec Γ (v.replace n 0 repl) ty := by -/
/-   intro h hReplTy hspec -/
/-   induction v generalizing ty Γ replTy -/
/-   <;> dsimp [Stx.replace] -/
/-   case bvar => -/
/-     split -/
/-     · sorry -/
/-     · exact hspec -/
/-   · exact hspec -/
/-   case app => -/
/-     sorry -/
/-   case abs => -/
/-     sorry -/

/- theorem TypePreservation.beta (arg : Stx) -/
/-     (arg_ih : ∀ {e₂ : Stx} {Γ : List Ty} {ty₁ ty₂ : Ty}, Red arg e₂ → TySpec Γ arg ty₁ → TySpec Γ e₂ ty₂ → ty₁ = ty₂) -/
/-     (fn_ih : ∀ {e₂ : Stx} {Γ : List Ty} {ty₁ ty₂ : Ty}, -/
/-         Red ((λ: argTy) body) e₂ → TySpec Γ ((λ: argTy) body) ty₁ → TySpec Γ e₂ ty₂ → ty₁ = ty₂) -/
/-     (hty₂ : TySpec Γ (Stx.replace n 0 body arg) ty₂) (hty₁ : TySpec Γ arg argTy₁) -/
/-     (hfull₁ : TySpec Γ ((λ: argTy) body) (argTy₁ ⇒ ty₁)) : ty₁ = ty₂ := by -/
/-   clear arg_ih fn_ih -/
/-   cases hfull₁ -/
/-   next hBodyCtx => -/
/-   induction body -/
/-   <;> dsimp [Stx.replace] at * -/
/-   case bvar id => -/
/-     split at hty₂ -/
/-     <;> cases hBodyCtx -/
/-     · sorry -/
/-     · cases hty₂ -/
/-       sorry -/
/-     /- cases hBodyCtx -/ -/
/-     /- sorry -/ -/
/-   · cases hty₂ -/
/-     cases hBodyCtx -/
/-     rfl -/
/-   · sorry -/
/-   case abs ty' body body_ih => -/
/-     cases hBodyCtx -/
/-     next retTy'₁ h₁ => -/
/-     cases hty₂ -/
/-     next retTy'₂ h₂ => -/
/-     apply body_ih -/
/-     · sorry -/
/-     · sorry -/
/-   stop -/
/-   induction n, body, arg using Stx.replace.induct -/
/-   <;> simp [Stx.replace] at hty₂ -/
/-   · cases hfull₁ -/
/-     next hfull₁ => -/
/-     cases hfull₁ -/
/-     next h =>  -/
/-     sorry -/
/-   · sorry -/
/-   · sorry -/
/-   · sorry -/
/-   · sorry -/

/- theorem shiftMaintains concat : TySpec (concat ++ Γ) (Stx.bvarShift concat.length 0 arg) ty₂ → TySpec Γ arg ty₂ := by -/
/-   intro h -/
/-   induction arg generalizing ty₂ concat -/
/-   <;> dsimp [Stx.bvarShift] at * -/
/-   <;> cases h -/
/-   case bvar idx fn => -/
/-     rw [List.getElem?_append_right (by omega), add_tsub_cancel_right] at fn -/
/-     exact .bvar fn -/
/-   case fvar => -/
/-     exact .fvar -/
/-   case app fn_ih arg_ih _ harg hfn => -/
/-     exact .app (fn_ih concat hfn) (arg_ih concat harg) -/
/-   case abs ty _ body_ih _ hbody => -/
/-     rw [←List.cons_append _ _ _] at hbody -/
/-     have := body_ih (ty :: concat) hbody -/
/-     sorry -/

lemma List.getElem?_length {ls : List α} : ls[n]? = some v → n < ls.length := by
  intro h
  induction ls generalizing n
  · contradiction
  case cons hd tl tl_ih =>
    cases n
    · exact Nat.zero_lt_succ _
    case succ n =>
      simp only [List.length_cons, add_lt_add_iff_right]
      apply tl_ih
      simp only [List.getElem?_cons_succ] at h
      exact h

lemma List.eraseIdx_pre_k
    {k : Nat} {ls : List α} (shorter : k < n)
    (hv : (ls.eraseIdx n)[k]? = some z) : (ls[k]? = some z) := by
  induction ls, n using List.eraseIdx.induct generalizing k
  <;> dsimp [List.eraseIdx] at hv
  <;> (try contradiction)
  next hd tl n ih =>
    cases k
    · simp_all only [Nat.succ_eq_add_one, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
        List.length_cons, List.getElem?_eq_getElem, List.getElem_cons_zero, Option.some.injEq]
    next n' =>
      simp_all only [Nat.succ_eq_add_one, add_lt_add_iff_right, List.getElem?_cons_succ]

theorem ReverseBetaTypingX.ex1
    {id : ℕ} {Γ : List Ty} {Γ' : List Ty}
    (hArgTy : TySpec Γ arg argTy) (lookup : Γ'[n]? = some argTy)
    (nLtLen : n < Γ'.length)
    (ha : (Γ'.eraseIdx n ++ Γ)[id]? = some ty₂)
    (lower : id < n) : n < (Γ'.eraseIdx n).length := by
  sorry
  /- induction Γ', n using List.eraseIdx.induct generalizing id Γ -/
  /- <;> (try contradiction) -/
  /- next hd tl n ih => -/
    /- dsimp [List.eraseIdx] at * -/
    /- simp only [List.getElem?_cons_succ] at lookup -/
    /- simp only [add_lt_add_iff_right] at nLtLen -/
    /- specialize ih hArgTy lookup nLtLen -/
    /- sorry -/
    /- cases id -/
    /- <;> simp_all only [List.getElem?_eq_getElem, Option.some.injEq, List.length_cons, -/
    /-     List.length_append, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, -/
    /-     List.getElem_cons_zero, add_lt_add_iff_right, List.getElem?_cons_succ] -/
    /- · sorry -/
    /- case succ n => -/
    /-   sorry -/
  /- have := (List.getElem?_append (by sorry)).symm.trans ha -/
  /- sorry -/

theorem ReverseBetaTypingX.bvar (id : ℕ) {Γ : List Ty} {arg : Stx} {argTy : Ty} {Γ' : List Ty} {n : ℕ} {ty₂ : Ty}
    (hArgTy : TySpec Γ arg argTy) (lookup : Γ'[n]? = some argTy)
    (repl : TySpec (Γ'.eraseIdx n ++ Γ) (Stx.replace.bvar id n arg) ty₂) : TySpec (Γ' ++ Γ) (b:id) ty₂ := by
  dsimp [Stx.replace.bvar] at repl
  refine .bvar ?_
  have nLtLen := List.getElem?_length lookup
  split at repl
  next h =>
    rw [h, List.getElem?_append (List.getElem?_length lookup), lookup, Option.some.injEq] at *
    clear lookup h
    induction arg generalizing Γ' Γ argTy ty₂
    <;> dsimp [Stx.bvarShift] at repl
    <;> cases hArgTy
    <;> cases repl
    case bvar =>
      sorry
    case fvar => rfl
    case app fn_ih arg_ih _ harg₂ hfn₂ _ harg₁ hfn₁ =>
      exact ((Ty.arr.injEq _ _ _ _).mp (fn_ih hfn₂ nLtLen hfn₁)).2
    case abs body_ih _ hbody₂ _ hbody₁ =>
      rw [←List.cons_append _ _ _] at hbody₁
      have := body_ih _ nLtLen hbody₁
      sorry
  /-   case bvar id ha hb => -/
  /-     have hb := List.getElem?_length hb -/
  /-     have ha := List.getElem?_length ha -/
  /-     simp at hb -/
  /-     sorry -/
  /-   case fvar => rfl -/
  /-   · sorry -/
  /-   case abs ty body body_ih => -/
  /-     sorry -/

  split at repl
  next h =>
    sorry
  /-   have nLtLen := List.getElem?_length lookup -/
  /-   cases repl -/
  /-   next idGtN ha => -/
  /-   sorry -/
  /-   /- rw [List.getElem_append id nLtLen] -/ -/
  /-   /- have := (List.getElem?_append (by -/ -/
  /-   /-   have := List.getElem?_length ha -/ -/
  /-   /-   simp at this -/ -/
  /-   /-   rw [List.length_eraseIdx nLtLen] -/ -/
  /-   /-   sorry -/ -/
  /-   /-   /- apply Nat.sub_lt_sub_right -/ -/ -/
  /-   /-   /- · exact Nat.one_le_of_lt idGtN -/ -/ -/
  /-   /-   /- · calc -/ -/ -/
  /-   /- )).symm.trans ha -/ -/
  next =>
    cases repl
    next idNEq idNGt ha =>
    simp only [gt_iff_lt, not_lt] at idNGt
    rw [List.getElem?_append _]
    repeat sorry
  /-   · have lower := Nat.lt_of_le_of_ne idNGt idNEq -/
  /-     have := (List.getElem?_append (by -/
  /-       calc -/
  /-         _ < n := lower -/
  /-         _ < _ := by -/
  /-           exact ReverseBetaTypingX.ex1 hArgTy lookup nLtLen ha lower -/
  /-     )).symm.trans ha -/
  /-     exact List.eraseIdx_pre_k lower this -/
  /-   · calc -/
  /-     _ ≤ n := idNGt -/
  /-     _ < _ := nLtLen -/

theorem ReverseBetaTypingX
    (hArgTy : TySpec Γ arg argTy) (lookup : Γ'[n]? = some argTy)
    (repl : TySpec (Γ'.eraseIdx n ++ Γ) (Stx.replace n body arg) ty₂)
    : TySpec (Γ' ++ Γ) body ty₂ := by
  induction body generalizing arg argTy ty₂ Γ' n Γ
  <;> dsimp [Stx.replace] at repl
  case bvar id =>
    exact ReverseBetaTypingX.bvar id hArgTy lookup repl
  case fvar =>
    cases repl
    exact .fvar
  case app fn_ih arg_ih =>
    cases repl
    next harg hfn =>
    exact .app (fn_ih hArgTy lookup hfn) (arg_ih hArgTy lookup harg)
  case abs ty body body_ih =>
    cases repl
    next retTy hrepl =>
    refine .abs ?_
    rw [←List.cons_append _ _ _]
    apply body_ih (n := n+1) hArgTy
    · simp only [List.getElem?_cons_succ]
      assumption
    · rw [←List.cons_append _ _ _, ← List.eraseIdx_cons_succ] at hrepl
      exact hrepl

theorem ReverseBetaTyping
    (hArgTy : TySpec Γ arg argTy) (lookup : Γ'[n]? = some argTy)
    (repl : TySpec (Γ) (Stx.replace n body arg) ty₂) : TySpec (Γ' ++ Γ) body ty₂ := by
  induction body generalizing arg argTy ty₂ Γ' n Γ
  <;> dsimp [Stx.replace] at repl
  case bvar id =>
    sorry
    /- exact ReverseBetaTypingX.bvar id hArgTy lookup repl -/
  case fvar =>
    cases repl
    exact .fvar
  case app fn_ih arg_ih =>
    cases repl
    next harg hfn =>
    exact .app (fn_ih hArgTy lookup hfn) (arg_ih hArgTy lookup harg)
  case abs ty body body_ih =>
    cases repl
    next retTy hrepl =>
    refine .abs ?_
    rw [←List.cons_append _ _ _]
    /- rw [←List.cons_append _ _ _, ← List.eraseIdx_cons_succ] at hrepl -/
    /- stop -/
    apply body_ih (n := n+1) hArgTy
    · simp only [List.getElem?_cons_succ]
      assumption
    · sorry
      /- exact hrepl -/
/- theorem ReverseBetaTyping -/
/-     (hArgTy : TySpec Γ arg argTy) (lookup : Γ'[n]? = some argTy) -/
/-     (repl : TySpec Γ (Stx.replace n body arg) ty₂) : TySpec Γ' body ty₂ := by -/
/-   induction body generalizing arg argTy ty₂ Γ' n Γ -/
/-   <;> dsimp [Stx.replace] at repl -/
/-   · split at repl -/
/-     next h => -/
/-       rw [h] -/
/-       refine .bvar ?_ -/
/-       sorry -/
/-       /- simp only [List.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, -/ -/
/-       /-   List.getElem?_eq_getElem, List.getElem_cons_zero, Option.some.injEq] -/ -/
/-     · sorry -/
/-   · cases repl -/
/-     exact .fvar -/
/-   case app fn_ih arg_ih => -/
/-     cases repl -/
/-     next harg hfn => -/
/-     sorry -/
/-   case abs ty body body_ih => -/
/-     cases repl -/
/-     next retTy hrepl => -/
/-     refine .abs ?_ -/
/-     apply body_ih (n := n+1) hArgTy -/
/-     · simp only [List.getElem?_cons_succ] -/
/-       assumption -/
/-     sorry -/

theorem TypePreservation : Red e₁ e₂ → TySpec Γ e₁ ty₁ → TySpec Γ e₂ ty₂ → ty₁ = ty₂ := by
  intro h hty₁ hty₂
  induction e₁ generalizing e₂ ty₁ ty₂
  <;> cases h
  case appl a b a_ih _ a' ha =>
    cases hty₁
    next bty₁ hb₁ ha₁ =>
    cases hty₂
    next bty₂ hb₂ ha₂ =>
    exact ((Ty.arr.injEq _ _ _ _).mp $ a_ih ha ha₁ ha₂).2

  case appr a b a_ih _ b' hb =>
    cases hty₁
    next bty₁ hb₁ ha₁ =>
    cases hty₂
    next bty₂ hb₂ ha₂ =>
    exact ((Ty.arr.injEq _ _ _ _).mp $ TyUnique ha₁ ha₂).2

  case beta arg _ argTy body _ =>
    cases hty₁
    next argTy hArgTy hfn =>
    cases hfn
    next hfn =>
    dsimp [Stx.β] at hty₂

    change TySpec ([argTy] ++ Γ) _ _  at hfn
    change TySpec ([argTy].eraseIdx 0 ++ Γ) _ _  at hty₂

    refine TyUnique hfn (ReverseBetaTypingX hArgTy ?_ hty₂)
    simp only [List.length_singleton, zero_lt_one, List.getElem?_eq_getElem, List.getElem_cons_zero]
    /- clear arg_ih fn_ih -/
    /- rcases hty₁ -/
    /- next argTy' a b => -/
    /- cases b -/
    /- next hbody => -/
    /- induction body -/
    /- <;> dsimp [Stx.β, Stx.replace] at hty₂ -/
    /- case bvar id => -/
    /-   split at hty₂ -/
    /-   · cases hbody -/
    /-     simp_all only [List.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, -/
    /-       List.getElem?_eq_getElem, List.getElem_cons_zero, Option.some.injEq] -/
    /-     exact TyUnique a (shiftMaintains [] hty₂) -/

    /-   · cases id -/
    /-     contradiction -/
    /-     simp only [gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, ↓reduceIte, -/
    /-       add_tsub_cancel_right] at hty₂ -/
    /-     cases hbody -/
    /-     cases hty₂ -/
    /-     simp_all only [add_eq_zero, one_ne_zero, and_false, not_false_eq_true, -/
    /-       List.getElem?_cons_succ, Option.some.injEq] -/

    /- · cases hty₂ -/
    /-   cases hbody -/
    /-   rfl -/
    /- case app fn_ih arg_ih => -/
    /-   cases hty₂ -/
    /-   cases hbody -/
    /-   next arg₂ fn₂ _ arg₁ fn₁=> -/
    /-   sorry -/
    /- case abs body_ih => -/
    /-   cases hty₂ -/
    /-   cases hbody -/
    /-   sorry -/

    /- /- cases hty₁ -/ -/
    /- /- next argTy₁ hty₁  hfull₁ => -/ -/
    /- /- exact TypePreservation.beta arg arg_ih fn_ih hty₂ hty₁ hfull₁ -/ -/
