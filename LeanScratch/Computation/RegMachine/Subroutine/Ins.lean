import LeanScratch.Computation.RegMachine

namespace Comp

variable {InsA InsB} [Fintype2 InsA] [Fintype2 InsB]

def subroutine.insMapper
    {r : RegTree}
    (inM : RegMachine r InsA)
    (imapper : InsA → InsB)
    (hltStepper : InsB)
    (x : InsA) : RegMachine.Ins r InsB :=
  match inM x with
  | .inc r next =>
    let next := match inM next with
      | .hlt => hltStepper
      | _    => imapper next
    .inc r next
  | .dec r nz z =>
    let nz := match inM nz with
      | .hlt => hltStepper
      | _    => imapper nz
    let z  := match inM z with
      | .hlt => hltStepper
      | _    => imapper z
    .dec r nz z
  | .hlt => .hlt -- This case should be handled differently maybe

-- TODO: Split this into a simpler lemma where I just do it on a single step
--       and a driver lemma that does the whole computation.
theorem subroutine.insMapper.forward
    {r : RegTree}
    {prog : RegMachine r InsB}
    {inM  : RegMachine r InsA}

    {imapper iInitStore iEndStore}

    -- the following theorems should all be solvable with large simps
    (hIsSub : prog ∘ imapper = insMapper inM imapper hltStepper)
    (hStartNotHlt : inM startS ≠ .hlt)

    (hInTW : inM.TW ⟨iInitStore, startS⟩ ⟨iEndStore, endS⟩)

    : prog.StepsTo ⟨iInitStore, imapper startS⟩
                   ⟨iEndStore, hltStepper⟩ := by
  rcases hInTW with ⟨w, term, v⟩
  exists w
  induction w generalizing startS iInitStore
  · obtain ⟨rfl, rfl⟩ := (RegMachine.Config.mk.injEq _ _ _ _).mp $ (Option.some.injEq _ _).mp term
    exact (hStartNotHlt $ RegMachine.Config.step.none_hlt v).elim
  case succ n ih =>
    -- Unfold what information we get about the termination
    obtain ⟨⟨imStore, imState⟩, stepper, p⟩ := Option.bind_eq_some.mp term; clear term

    apply Option.bind_eq_some.mpr

    -- Open the step defn
    simp only [Function.funext_iff, Function.comp_apply] at hIsSub
    dsimp [RegMachine.Config.step]
    rw [hIsSub]; clear hIsSub

    dsimp [insMapper]
    cases heq : inM startS
    <;> dsimp
    <;> simp only [RegMachine.Config.step, heq, Option.some.injEq, RegMachine.Config.mk.injEq] at stepper
    <;> clear heq
    on_goal 1 =>  rename_i reg nextins
    on_goal 2 => (rename_i reg nzdest zdest; split <;> rename_i heq <;>
      simp only [heq, Option.some.injEq, RegMachine.Config.mk.injEq] at stepper)

    all_goals rcases stepper with ⟨rfl, rfl⟩

    -- Split each case
    on_goal 1 => by_cases hNextEq : inM nextins = .hlt
    on_goal 3 => by_cases hNextEq : inM nzdest  = .hlt
    on_goal 5 => by_cases hNextEq : inM zdest   = .hlt

    -- Close negative goals
    any_goals (simp only [Option.some.injEq, exists_eq_left']; exact ih hNextEq p)

    -- Assign each store value
    on_goal 1 => exists ⟨RegMachine.inc reg iInitStore, hltStepper⟩
    on_goal 3 => exists ⟨iInitStore,                    hltStepper⟩
    on_goal 2 => rename_i s;                 exists ⟨s, hltStepper⟩

    -- Close all goals
    all_goals {
      simp only [hNextEq, true_and]
      obtain rfl : n = 0 := by
        cases n
        · rfl
        · simp [RegMachine.Config.step_n, RegMachine.Config.step, hNextEq] at p
      simp_all
    }

