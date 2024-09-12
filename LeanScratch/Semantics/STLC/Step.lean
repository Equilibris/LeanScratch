import LeanScratch.Semantics.STLC.Stx
import LeanScratch.Semantics.STLC.Red
import Mathlib.Data.Rel
import LeanScratch.Relation

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

lemma RedPlus_congr (h : RedPlus body w) : RedPlus (.abs ty body) (.abs ty w) := by
  induction h
  case single h     => exact .single $ .congr h
  case tail body ih => exact .tail ih $ .congr body

lemma RedPlus_appl (h : RedPlus a w) : RedPlus (.app a b) (.app w b) := by
  induction h
  case single h     => exact .single $ .appl h
  case tail body ih => exact .tail ih $ .appl body

lemma RedPlus_appr (h : RedPlus a w) : RedPlus (.app b a) (.app b w) := by
  induction h
  case single h     => exact .single $ .appr h
  case tail body ih => exact .tail ih $ .appr body

theorem step_some_RedPlus (h : step main = .some a₁) : RedPlus main a₁ := 
  match main with
  | .bvar id => by simp only [step] at h
  | .abs ty body => by
    simp only [step, Option.map_eq_some'] at h
    rcases h with ⟨w, h, rfl⟩
    exact RedPlus_congr $ step_some_RedPlus h
  | .app a b => by
    by_cases isAbs : ∃ ty body, a = .abs ty body
    · rcases isAbs with ⟨ty,body, rfl⟩
      simp only [step, Option.some.injEq] at h
      rw [←h]
      exact .single .beta
    · simp only [not_exists] at isAbs
      unfold step at h
      split at h
      <;> try contradiction
      next heq => simp_all only [Stx.app.injEq, false_and]
      next heq =>
        split at h
        <;> simp only [Option.some.injEq] at h
        <;> rw [←h, heq]
        next a b _ _ _ a' ha hb =>
          exact RedPlus_appl $ step_some_RedPlus ha
        next ha hb =>
          exact RedPlus_appr $ step_some_RedPlus hb
        next a b _ _ _ a' b' ha hb =>
          calc
            RedPlus _ (.app _ _) := RedPlus_appr $ step_some_RedPlus hb
            RedPlus _ (.app _ _) := RedPlus_appl $ step_some_RedPlus ha
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
      simp only [Stx.app.injEq] at heq
      rcases heq with ⟨haa, hbb⟩
      simp_all only [false_implies, implies_true, Stx.Terminal_app]
      have ha := step_none_terminal ha
      have hb := step_none_terminal hb
      cases ha
      · exfalso
        exact isAbs _ _ rfl
      next ha => exact ⟨ha, hb⟩
