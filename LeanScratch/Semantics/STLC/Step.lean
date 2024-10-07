import LeanScratch.Semantics.STLC.Stx
import LeanScratch.Semantics.STLC.Red
import LeanScratch.Semantics.STLC.StrongNorm
import Mathlib.Data.Rel
import LeanScratch.Relation
import LeanScratch.Rel2

namespace STLC

def step : Stx → Option Stx
  | .bvar _ => .none
  | .abs ty body => (step body).map (.abs ty ·)
  | .app (.abs _ body) repl => .some $ body.β repl
  | .app a b => match step a, step b with
    | .none, .none => .none
    | .some a, .none
    | .none, .some b
    | .some a, .some b => .some $ .app a b

lemma RedPlus_congr : RedPlus body w → RedPlus (.abs ty body) (.abs ty w) :=
  Relation.transGenMap .congr

lemma RedPlus_appl : RedPlus a w → RedPlus (.app a b) (.app w b) :=
  Relation.transGenMap (fun {x y} => @Red.appl x y b)

lemma RedPlus_appr  : RedPlus a w → RedPlus (.app b a) (.app b w) :=
  Relation.transGenMap (fun {x y} => @Red.appr x y b)

theorem step_some_RedPlus (h : step main = .some a₁) : RedPlus main a₁ := 
  match main with
  | .bvar id => by simp only [step] at h
  | .abs ty body => by
    rw [step, Option.map_eq_some'] at h
    rcases h with ⟨w, h, rfl⟩
    exact RedPlus_congr $ step_some_RedPlus h
  | .app a b => by
    by_cases isAbs : ∃ ty body, a = .abs ty body
    · rcases isAbs with ⟨ty,body, rfl⟩
      rw [step, Option.some.injEq] at h
      rw [←h]
      exact .single .beta
    · simp only [not_exists] at isAbs
      unfold step at h
      split at h
      <;> try contradiction
      next heq =>
        simp_all only [Stx.app.injEq, false_and]
      next heq =>
        split at h
        <;> simp only [Option.some.injEq] at h
        <;> rw [←h, heq]
        next ha _ =>
          exact RedPlus_appl $ step_some_RedPlus ha
        next hb =>
          exact RedPlus_appr $ step_some_RedPlus hb
        next ha hb =>
          exact (RedPlus_appr $ step_some_RedPlus hb).trans (RedPlus_appl $ step_some_RedPlus ha)
termination_by SizeOf.sizeOf main
decreasing_by
  all_goals simp_wf
  <;> simp_all only [Stx.app.injEq, Option.some.injEq]
  <;> linarith

theorem step_none_terminal (h : step main = .none) : Stx.Terminal main :=
  match main with
  | .bvar id => .nonEval .bvar
  | .abs ty body => by
    simp only [step, Option.map_eq_none', Stx.Terminal_abs] at h ⊢
    exact step_none_terminal h
  | .app a b => by
    by_cases isAbs : ∃ ty body, a = .abs ty body
    · rcases isAbs with ⟨ty,body, rfl⟩
      simp only [step] at h
    · simp only [not_exists] at isAbs
      unfold step at h
      split at h
      <;> try contradiction
      split at h
      <;> try contradiction
      next heq _ _ ha hb =>
      rw [Stx.app.injEq] at heq
      rcases heq with ⟨haa, hbb⟩
      simp_all only [false_implies, implies_true, Stx.Terminal_app]
      have ha := step_none_terminal ha
      have hb := step_none_terminal hb
      cases ha
      · exfalso
        exact isAbs _ _ rfl
      next ha => exact ⟨ha, hb⟩

def full_red_direct'
    body
    (spec : TySpec Γ body ty)
    (Γ' : TyArr Γ)
    (hΓ' : TyArr.Every ArgCount.Monotonic Γ') 
    : Stx :=
  match h : step body with
  | .none => body
  | .some nBody => full_red_direct' nBody (LongTypePreservation spec ((step_some_RedPlus h).to_reflTransGen)) Γ' hΓ'
termination_by (upperBoundRed (TySpec_CTySpec spec) Γ').naturalize
decreasing_by
· simp_wf
  exact RedPlus_nat_dec hΓ' (step_some_RedPlus h) _ _

def full_red_direct
    body
    (spec : TySpec Γ body ty)
    : Stx :=
  let ⟨a, b⟩ := allZeros Γ
  full_red_direct' body spec a b
where
  allZeros : (Γ : List Ty) → (Γ' : TyArr Γ) ×' (TyArr.Every ArgCount.Monotonic Γ')
    | [] => ⟨.nil, .nil⟩
    | _ :: tl =>
      let ⟨a, b⟩ := allZeros tl
      ⟨.cons ArgCount.zero a, .cons ArgCount.zero_Monotonic b⟩

def full_red (body : Stx) (Γ : List Ty) : Option Stx :=
  match h : infer Γ body with
  | some _ => full_red_direct body (infer_TySpec.mp h)
  | none => none

