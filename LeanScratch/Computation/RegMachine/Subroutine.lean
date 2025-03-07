import LeanScratch.Computation.RegMachine
import LeanScratch.Computation.RegMachine.UpdateImage

namespace Comp

variable {Ins InsB} [Fintype2 Ins] [Fintype2 InsB]

def subroutine.insMapper
    {r : RegTree}
    (inM : RegMachine r Ins)
    (imapper : Ins → InsB)
    (hltStepper : InsB)
    (x : Ins) : RegMachine.Ins r InsB :=
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

def subroutine.regMapper
    {r t : RegTree}
    (inM : RegMachine r Ins)
    (rmapper : r.toIdx → t.toIdx)
    : RegMachine t Ins :=
  (match inM · with
  | .inc reg ins => .inc (rmapper reg) ins
  | .dec reg nz z => .dec (rmapper reg) nz z
  | .hlt => .hlt)

/- def subroutine -/
/-     {r t : RegTree} -/
/-     (inM : RegMachine r Ins) -/
/-     (rmapper : r.toIdx → t.toIdx) -/
/-     (imapper : Ins → InsB) -/
/-     (hltStepper : InsB) -/
/-     (x : Ins) -/
/-     : RegMachine.Ins t InsB := -/
/-   subroutine.regMapper (subroutine.regMapper inM rmapper) _ _ x -/

theorem RegMachine.step.none_hlt [Fintype2 L] {inM : RegMachine r L}
    (h : RegMachine.Config.step inM ⟨view, s⟩ = none)
    : inM s = .hlt :=
  match heq : inM s with
  | .hlt => rfl
  | .inc _ _ | .dec _ _ _ => by
    simp only [Config.step, heq] at h
    <;> split at h
    <;> exact Option.noConfusion h

theorem subroutine.regMapper.singleForward
    {r t : RegTree}
    {inM : RegMachine r Ins}
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

-- TODO: Split this into a simpler lemma where I just do it on a single step
--       and a driver lemma that does the whole computation.
theorem subroutine.insMapper.forward
    {r : RegTree}
    {prog : RegMachine r InsB}
    {inM  : RegMachine r Ins}

    {imapper iInitStore iEndStore}

    -- the following theorems should all be solvable with large simps
    (hIsSub : prog ∘ imapper = insMapper inM imapper hltStepper)

    (hInTW : inM.TW ⟨iInitStore, startS⟩ ⟨iEndStore, endS⟩)
    (hStartNotHlt : inM startS ≠ .hlt)

    : prog.StepsTo ⟨iInitStore, imapper startS⟩
                   ⟨iEndStore, hltStepper⟩ := by
  rcases hInTW with ⟨w, term, v⟩
  exists w
  induction w generalizing startS iInitStore
  · obtain ⟨rfl, rfl⟩ := (RegMachine.Config.mk.injEq _ _ _ _).mp $ (Option.some.injEq _ _).mp term
    exact (hStartNotHlt $ RegMachine.step.none_hlt v).elim
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
    case inc reg nextins =>
      rcases stepper with ⟨rfl, rfl⟩
      by_cases hNextEq : inM nextins = .hlt
      · exists ⟨RegMachine.inc reg iInitStore, hltStepper⟩
        simp only [hNextEq, true_and]
        obtain rfl : n = 0 := by
          cases n
          · rfl
          · simp [RegMachine.Config.step_n, RegMachine.Config.step, hNextEq] at p
        simp_all
      · simp only [Option.some.injEq, exists_eq_left', hNextEq]
        apply ih hNextEq
        rw [←p]
    case dec r nzdest zdest =>
      split
      <;> rename_i heq
      <;> simp only [heq, Option.some.injEq, RegMachine.Config.mk.injEq] at stepper
      <;> rcases stepper with ⟨rfl, rfl⟩
      next x s =>
        by_cases hNextEq : inM nzdest = .hlt
        · exists ⟨s, hltStepper⟩
          simp only [hNextEq, true_and]
          obtain rfl : n = 0 := by
            cases n
            · rfl
            · simp [RegMachine.Config.step_n, RegMachine.Config.step, hNextEq] at p
          simp_all
        · simp only [Option.some.injEq, exists_eq_left']
          apply ih hNextEq
          rw [←p]
      next s =>
        by_cases hNextEq : inM zdest = .hlt
        · exists ⟨iInitStore, hltStepper⟩
          obtain rfl : n = 0 := by
            cases n
            · rfl
            · simp [RegMachine.Config.step_n, RegMachine.Config.step, hNextEq] at p
          simp_all
        · simp only [Option.some.injEq, exists_eq_left']
          apply ih hNextEq p

theorem subroutine.forward
    {r t : RegTree}
    {prog : RegMachine t InsB}

    {inM : RegMachine r Ins}
    {rmapper : r.toIdx → t.toIdx}
    {imapper : Ins → InsB}

    {iInitStore iEndStore outerStore}

    -- the following theorems should all be solvable with large simps
    (hIsSub : prog ∘ imapper = subroutine inM rmapper imapper hltStepper)

    (hRInj : Function.Injective rmapper)
    (hIInj : Function.Injective imapper)

    (hInTW : inM.TW ⟨iInitStore, startS⟩ ⟨iEndStore, endS⟩)
    (hStartNotHlt : inM startS ≠ .hlt)

    : prog.StepsTo ⟨updateImage rmapper iInitStore outerStore, imapper startS⟩
                   ⟨updateImage rmapper iEndStore  outerStore, hltStepper⟩ := by
  rcases hInTW with ⟨w, term, v⟩
  induction w generalizing startS iInitStore
  · obtain ⟨rfl, rfl⟩ := (RegMachine.Config.mk.injEq _ _ _ _).mp $ (Option.some.injEq _ _).mp term
    exact (hStartNotHlt $ RegMachine.step.none_hlt v).elim
  case succ n ih =>
    obtain ⟨⟨imStore, imState⟩, stepper, p⟩ := Option.bind_eq_some.mp term
    clear term

    exists n+1
    simp only [RegMachine.Config.step_n]
    apply Option.bind_eq_some.mpr
    dsimp [RegMachine.Config.step, subroutine]
    simp [Function.funext_iff] at hIsSub
    rw [hIsSub]
    dsimp [subroutine]
    cases heq : inM startS
    <;> (try exact (hStartNotHlt heq).elim)
    <;> rename_i reg nextins
    <;> by_cases hNextEq : inM nextins = .hlt
    · clear ih
      use ⟨RegMachine.inc (rmapper reg) (updateImage rmapper iInitStore outerStore), hltStepper⟩
      simp [hNextEq]
      simp only [RegMachine.Config.step, heq, Option.some.injEq, RegMachine.Config.mk.injEq] at stepper
      rcases stepper with ⟨rfl, rfl⟩
      obtain rfl : n = 0 := by
        cases n
        · rfl
        · simp [RegMachine.Config.step_n, RegMachine.Config.step, hNextEq] at p
      simp_all only [ne_eq, not_false_eq_true, RegMachine.Config.step_n.zero, Option.some.injEq,
        RegMachine.Config.mk.injEq, and_true]
      rcases p with ⟨rfl, rfl⟩
      sorry
      /- by_cases hInImage : ∃ v', v = rmapper v' -/
      /- sorry -/
      /- · have := hNeqStores _ hInImage -/
      /-   sorry -/
    · sorry
    · sorry
    · sorry

