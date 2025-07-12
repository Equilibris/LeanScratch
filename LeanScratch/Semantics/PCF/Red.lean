import LeanScratch.Semantics.PCF.Stx
/- import LeanScratch.Semantics.PCF.Typed -/
import Mathlib.Data.Rel
import Mathlib.Data.List.AList
import LeanScratch.Relation

namespace PCF

inductive Red : Expr [] τ → Expr [] τ → Prop
  | val : v.IsValue → Red v v
  | succ :
    Red t v
    → Red t.succ v.succ
  | pred :
    Red t v.succ
    → Red t.pred v
  | z?zero :
    Red t .zero
    → Red t.z? .tt
  | z?succ : Red t (.succ v)
    → Red t.z? .ff
  | eif_tt : Red c .tt
    → Red t v
    → Red (c.eif t f) v
  | eif_ff : Red c .ff
    → Red f v
    → Red (c.eif t f) v
  | abs_cbn /- (en : Cbn) -/ :
    {t : Expr [] $ .arrow arg o}
    → Red t (.abs arg t')
    → Red (t'.β u) v
    → Red (.app t u) v
  | fix : Red (.app t t.fix) v
    → Red t.fix v

theorem Red.res_val (h : Red e v) : v.IsValue := by
  induction h
  any_goals solve_by_elim
  case pred ih =>
    cases ih; assumption

theorem Red.val_hold (hV : e.IsValue) (h : Red e v) : e = v := by
  induction hV <;> cases h
  any_goals rfl
  case succ ih _ h => rw [ih h]

theorem Red.confluent (ha : Red e v₁) (hb : Red e v₂) : v₁ = v₂ := by
  induction ha
  case val ih => exact Red.val_hold ih hb
  all_goals cases hb
  any_goals solve_by_elim
  any_goals (rename_i hv; cases hv; done)
  case succ.val h _ hv =>
    cases hv; rename_i hv
    rw [Red.val_hold hv h]
  case pred.pred ih h=> exact (Expr.succ.injEq _ _).mp $ ih h
  case z?zero.z?succ ih _ h => exact Expr.noConfusion $ ih h
  case z?succ.z?zero ih h => exact Expr.noConfusion $ ih h
  case eif_tt.eif_ff ih _ h _=> exact Expr.noConfusion $ ih h
  case eif_ff.eif_tt ih _ h _=> exact Expr.noConfusion $ ih h
  case abs_cbn.abs_cbn ihf iha _ hf ha =>
    obtain rfl := Expr.abs.inj $ ihf hf
    exact iha ha

def Context (τ : Ty) : Type := Sigma $ Expr [τ]

def ContEquiv (a b : Expr [] τ) : Prop := ∀ c : Context τ,
  ∀ v, Red (c.snd.β a) v ↔ Red (c.snd.β b) v

theorem ContEquiv.eqIn : ContEquiv a a := fun _ _ => Eq.to_iff rfl



