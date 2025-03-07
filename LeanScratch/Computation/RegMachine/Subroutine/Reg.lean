import LeanScratch.Computation.RegMachine
import LeanScratch.Computation.RegMachine.UpdateImage

namespace Comp

variable {InsA InsB} [Fintype2 InsA] [Fintype2 InsB]

def subroutine.regMapper
    {r t : RegTree}
    (inM : RegMachine r InsA)
    (rmapper : r.toIdx → t.toIdx)
    : RegMachine t InsA :=
  (match inM · with
  | .inc reg ins => .inc (rmapper reg) ins
  | .dec reg nz z => .dec (rmapper reg) nz z
  | .hlt => .hlt)

def subroutine.regMapper.neLift
    {r t : RegTree}
    {inM : RegMachine r InsA}
    {rmapper : r.toIdx → t.toIdx}
    (h : inM s ≠ .hlt)
    : regMapper inM rmapper s ≠ .hlt := by
  dsimp [regMapper]
  cases hEq : inM s <;> simp_all

theorem subroutine.regMapper.singleForward
    {r t : RegTree}
    {inM : RegMachine r InsA}
    {map : r.toIdx → t.toIdx}
    {inS outS defS}
    (hRInj : Function.Injective map)
    (hBStep : RegMachine.Config.step inM ⟨inS, s1⟩ = some ⟨outS, s2⟩)
    : RegMachine.Config.step (subroutine.regMapper inM map)
      ⟨updateImage map inS defS, s1⟩ =
      some ⟨updateImage map outS defS, s2⟩ := by
  dsimp [RegMachine.Config.step, regMapper] at *
  split at hBStep
  <;> rename_i hMEq
  · rcases hBStep with ⟨rfl, rfl⟩
    simp only [hMEq, Option.some.injEq, RegMachine.Config.mk.injEq, and_true]
    exact updateImage.inc_slide hRInj
  · split at hBStep
    <;> rcases hBStep with ⟨rfl, rfl⟩
    <;> rename_i hDecEq
    <;> simp only [hMEq]
    · rw [updateImage.dec_slide hRInj, hDecEq]
      rfl
    · rename_i r _ _
      rw [RegMachine.dec_none_iff_lookup_z] at hDecEq
      have this : RegMachine.dec _ (updateImage map inS defS) = none :=
        RegMachine.dec_none_iff_lookup_z.mpr
        $ Eq.trans (updateImage.lookup hRInj) hDecEq
      simp [this]
  · exact Option.noConfusion hBStep

theorem subroutine.regMapper.forward
    {r t : RegTree}
    {inM : RegMachine r InsA}
    {map : r.toIdx → t.toIdx}
    {inS outS defS}
    (hRInj : Function.Injective map)
    (hBStep : inM.TW ⟨inS, s1⟩ ⟨outS, s2⟩)
    : (subroutine.regMapper inM map).TW
        ⟨updateImage map inS defS, s1⟩
        ⟨updateImage map outS defS, s2⟩ := by
  rcases hBStep with ⟨n, p, hTerm⟩
  exists n
  induction n generalizing inS s1
  · rcases p with ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    dsimp [RegMachine.Config.step, regMapper]
    rw [RegMachine.Config.step.none_hlt hTerm]
  case succ ih =>
    dsimp [RegMachine.Config.step_n] at *
    have ⟨⟨imS, imI⟩, hSmall, hLong⟩ := Option.bind_eq_some.mp p; clear p
    rw [regMapper.singleForward hRInj hSmall, Option.some_bind]
    exact ih hLong
