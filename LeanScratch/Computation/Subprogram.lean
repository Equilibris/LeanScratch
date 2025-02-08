import LeanScratch.Computation.RegMachine

namespace Comp

def transformReg
    {r t : RegTree}
    (f : r.toIdx → t.toIdx)
    (inM : RegMachine r L)
    : RegMachine t L := sorry

