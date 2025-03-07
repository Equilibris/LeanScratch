import LeanScratch.Computation.RegMachine
import LeanScratch.Computation.RegMachine.UpdateImage
import LeanScratch.Computation.RegMachine.Subroutine.Ins
import LeanScratch.Computation.RegMachine.Subroutine.Reg

namespace Comp

variable {InsA InsB} [Fintype2 InsA] [Fintype2 InsB]
def subroutine
    {r t : RegTree}
    : (RegMachine r InsA) → (r.toIdx → t.toIdx)
    → (InsA → InsB) → InsB → InsA
    → RegMachine.Ins t InsB :=
  (subroutine.insMapper $ subroutine.regMapper · ·)

theorem subroutine.forward
    {r t : RegTree}
    {prog : RegMachine t InsB}

    {inM : RegMachine r InsA}
    {rmapper : r.toIdx → t.toIdx}
    {imapper : InsA → InsB}

    {iInitStore iEndStore outerStore}

    -- the following theorems should all be solvable with large simps
    (hIsSub : prog ∘ imapper = subroutine inM rmapper imapper hltStepper)
    (hRInj : Function.Injective rmapper)
    (hStartNotHlt : inM startS ≠ .hlt)

    (hInTW : inM.TW ⟨iInitStore, startS⟩ ⟨iEndStore, endS⟩)

    : prog.StepsTo ⟨updateImage rmapper iInitStore outerStore, imapper startS⟩
                   ⟨updateImage rmapper iEndStore  outerStore, hltStepper⟩ :=
  subroutine.insMapper.forward hIsSub (regMapper.neLift hStartNotHlt)
    $ subroutine.regMapper.forward hRInj hInTW


