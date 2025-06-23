import LeanScratch.Vec

namespace Comp.CompFuns

def predf : Vec Nat 1 → Vec Nat 1 := fun | %[a] => %[a.pred]
def addf : Vec Nat 2 → Vec Nat 1 := fun | %[a, b] => %[a + b]
def projf : Vec Nat 2 → Vec Nat 1 := fun | %[a, _] => %[a]
def constf (n : Nat) : Vec Nat 1 → Vec Nat 1 := fun _ => %[n]
def subf : Vec Nat 2 → Vec Nat 1 := fun | %[a, b] => %[a - b]
def divmodf : Vec Nat 2 → Vec Nat 2 := fun | %[a, b] => %[a / b, a % b]
def exp2 : Vec Nat 1 → Vec Nat 1 := fun %[x] => %[Nat.pow 2 x]



