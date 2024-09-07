import LeanScratch.Semantics.L2Try2.Stx
import Mathlib.Data.Rel
import Mathlib.Data.List.AList
import LeanScratch.Relation

namespace L2
abbrev VarMap := AList (fun _ : String => Int)

abbrev State := BIdxExpr × VarMap

inductive Red : State → State → Prop
  | op_add (a b : Int) : Red ⟨.op (.int a) .add (.int b), s⟩ ⟨.int (a + b), s⟩
  | op_gte (a b : Int) : Red ⟨.op (.int a) .gte (.int b), s⟩ ⟨.bool (a >= b), s⟩

  | op1 : Red ⟨e, s⟩ ⟨e', s'⟩
      → Red ⟨.op e o e2, s⟩ ⟨.op e' o e2, s'⟩
  | op2 : Red ⟨e2, s⟩ ⟨e2', s'⟩
      → e.isInt → Red ⟨.op e o e2, s⟩ ⟨.op e o e2', s'⟩

  | deref : (h : s.lookup addr = some x)
      → Red ⟨.deref (addr), s⟩ ⟨.int x, s⟩
  | assign1 : (h : ∃ x, s.lookup addr = some x)
      → Red ⟨.assign addr (.int v), s⟩ ⟨.skip, s.insert addr v⟩
  | assign2 : Red ⟨e, s⟩ ⟨e', s'⟩ → Red ⟨.assign addr e, s⟩ ⟨.assign addr e', s'⟩

  | seq1 : Red ⟨.seq .skip e, s⟩ ⟨e, s⟩
  | seq2 : Red ⟨e1, s⟩ ⟨e1', s'⟩
      → Red ⟨.seq e1 e2, s⟩ ⟨.seq e1' e2, s'⟩

  | if_t : Red ⟨.eif (.bool true) e1 e2, s⟩ ⟨e1, s⟩
  | if_f : Red ⟨.eif (.bool false) e1 e2, s⟩ ⟨e2, s⟩

  | if_cond : Red ⟨condition, s⟩ ⟨condition', s'⟩
      → Red ⟨.eif condition e1 e2, s⟩ ⟨.eif condition' e1 e2, s'⟩

  | ewhile : Red ⟨.ewhile c body, stx⟩ ⟨.eif c (.seq body (.ewhile c body)) .skip, stx⟩

  | beta : repl.isFnValue
      → Red ⟨.app (.abs _ body) repl, s⟩ ⟨body.replace 0 repl, s⟩
  | app1 : Red ⟨e1, s⟩ ⟨e1', s'⟩
      → Red ⟨.app e1 e2, s⟩ ⟨.app e1' e2, s'⟩
  | app2 : e1.isFnValue → Red ⟨e2, s⟩ ⟨e2', s'⟩
      → Red ⟨.app e1 e2, s⟩ ⟨.app e1 e2', s'⟩
end L2
