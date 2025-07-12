import LeanScratch.Semantics.PCF.Stx
/- import LeanScratch.Semantics.PCF.Red -/
import LeanScratch.Relation
import Mathlib.Data.List.AList

namespace PCF

inductive TySpec : List Ty → Expr → Ty → Prop
  | tt : TySpec Γ .tt .bool
  | ff : TySpec Γ .ff .bool
  | zero : TySpec Γ .zero nat
  | succ : TySpec Γ a nat
      → TySpec Γ a.succ nat
  | pred : TySpec Γ a nat
      → TySpec Γ a.pred nat

  | z? : TySpec Γ a nat
      → TySpec Γ a.z? .bool

  | eif : TySpec Γ c .bool → TySpec Γ t a → TySpec Γ f a
      → TySpec Γ (.eif c t f) a

  | bvar : (Γ[idx]? = some w)
      → TySpec Γ (.bvar idx) w
  | abs : TySpec (argTy :: Γ) body retTy
      → TySpec Γ (.abs argTy body) (.arrow argTy retTy)
  | app : TySpec Γ fn (.arrow argTy retType) → TySpec Γ arg argTy
      → TySpec Γ (.app fn arg) retType

  | fix : TySpec Γ v (.arrow t t)
      → TySpec Γ v.fix t


theorem BvarShift.gen (hMain : TySpec (Γ₂ ++ Γ) body tout)
    : TySpec (Γ₂ ++ Γlead ++ Γ) (body.bvarShift Γlead.length Γ₂.length) tout :=
  match body, hMain with
  | .tt, .tt => .tt
  | .ff, .ff => .ff
  | .zero, .zero => .zero
  | .succ n, .succ hn => .succ $ gen hn
  | .pred n, .pred hn => .pred $ gen hn
  | .z? n, .z? hn => .z? $ gen hn

  | .eif c t f, .eif hc ht hf => .eif (gen hc) (gen ht) (gen hf)
  | .app a b, .app ha hb => .app (gen ha) (gen hb)
  | .fix f, .fix h => .fix $ gen h

  | .abs ty body, .abs hbody =>
    .abs $ gen $ show TySpec ((ty :: _) ++ _) _ _ from hbody
  | .bvar idx, .bvar hidx => by
    dsimp [Expr.bvarShift]
    refine .bvar ?_
    split <;> rename_i h
    · rw [List.append_assoc]
      rw [List.getElem?_append h] at hidx
      rwa [List.getElem?_append h]
    · rw [not_lt] at h
      rw [List.getElem?_append_right h] at hidx
      rw [List.append_assoc, List.getElem?_append_right (Nat.le_add_right_of_le h)]
      have h : Γlead.length ≤ idx + Γlead.length - Γ₂.length := by omega
      rwa [
        List.getElem?_append_right h,
        Nat.sub_right_comm,
        Nat.add_sub_assoc (Nat.le_refl _) _,
        Nat.sub_self
      ]

theorem Subst.gen (hTy : TySpec Γ e t) (hMain : TySpec (Γlead ++ (t :: Γ)) body tout)
    : TySpec (Γlead ++ Γ) (body.replace Γlead.length e) tout :=
  match body, hMain with
  | .tt, .tt => .tt
  | .ff, .ff => .ff
  | .zero, .zero => .zero
  | .succ n, .succ hn => .succ $ gen hTy hn
  | .pred n, .pred hn => .pred $ gen hTy hn
  | .z? n, .z? hn => .z? $ gen hTy hn

  | .eif c t f, .eif hc ht hf => .eif (gen hTy hc) (gen hTy ht) (gen hTy hf)
  | .app a b, .app ha hb => .app (gen hTy ha) (gen hTy hb)
  | .fix f, .fix h => .fix $ gen hTy h
  | .abs ty body, .abs hbody =>
    .abs $ gen hTy $ show TySpec ((ty :: _) ++ _) _ _ from hbody
  | .bvar idx, .bvar hidx => by
    dsimp [Expr.replace, Expr.replace.bvar]
    split <;> rename_i h
    <;> simp only [Nat.compare_eq_eq, Nat.compare_eq_lt, Nat.compare_eq_gt] at h
    · exact .bvar (by rwa [List.getElem?_append h] at hidx ⊢)
    · subst h
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hidx
      subst hidx
      exact BvarShift.gen (Γ₂ := []) hTy
    · refine .bvar ?_
      rw [List.getElem?_append_right (Nat.le_of_succ_le h)] at hidx
      rw [List.getElem?_append_right (Nat.le_sub_one_of_lt h), Nat.sub_right_comm]
      change ([_] ++ _)[_]? = _ at hidx
      rwa [List.getElem?_append_right
          $ show [t].length ≤ _ from Nat.le_sub_of_add_le' h] at hidx

theorem Subst
    : TySpec Γ e t
    → TySpec (t :: Γ) body tout
    → TySpec Γ (body.β e) tout
  := Subst.gen (Γlead := [])

