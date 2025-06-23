import LeanScratch.Vec
import Mathlib.Data.List.AList

inductive Colour where
  | red | cyan | black
deriving DecidableEq

instance : ToString Colour := ⟨fun | .red => "red" | .cyan => "cyan" | .black => "black"⟩

def Graph (n : Nat) := Vec (List $ Fin n) n

abbrev Assignments (n : Nat) := AList (fun _ : Fin2 n => Colour)

def currentGraph : Graph 8 := %[
  [1, 2, 3],
  [0, 3, 5],
  [0, 3, 6],
  [0, 1, 2, 4],
  [3, 5, 6],
  [1, 6, 7],
  [4, 5, 7],
  [5, 6]]

def printGraph (pfix : String) (g : Graph n) : String :=
  walker g
where
  walker {v} : Vec (List $ Fin n) v → String
    | %[] => ""
    | hd %:: tl =>
      hd.foldl (s!"{·}\n{pfix}{n - v} --> {pfix}{·}") $ walker tl

def printAssignemnt (pfix : String) (al : Assignments n) : String :=
  al.foldl (s!"{·}\nstyle {pfix}{·.toNat} fill : {·};") ""

#eval IO.println $ printGraph "p" currentGraph

def Fin2.lastOrNext (f : Fin2 n)( last : motive) (cont : Fin2 n → motive) : motive :=
  match n, f with
  | _+2, .fz => cont Fin2.fz.fs
  | 1, .fz => last
  | _+1, .fs x => x.lastOrNext last (cont ∘ .fs)

partial def solveCsp (g : Graph n) (ass : Assignments n) (node : Fin2 n) : IO (Assignments n) :=
  if ass.lookup node = .none then
    sorry
  else
    contOrTerm ass
where
  contOrTerm ass :=
    node.lastOrNext (pure ass) (solveCsp g ass)

