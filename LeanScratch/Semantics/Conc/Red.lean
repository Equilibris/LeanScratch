import LeanScratch.Semantics.Conc.Stx
import Batteries.Data.HashMap.Basic
import Mathlib.Data.Rel
import Mathlib.Data.List.AList
import LeanScratch.Relation

namespace L1Par

abbrev VarMap := AList (fun _ : String => Int)
abbrev MtxMap := AList (fun _ : String => Bool)

abbrev State := Expr × MtxMap × VarMap

inductive Red : State → State → Prop
  | op_add (a b : Int) : Red ⟨.op (.int a) .add (.int b), s⟩ ⟨.int (a + b), s⟩
  | op_gte (a b : Int) : Red ⟨.op (.int a) .gte (.int b), s⟩ ⟨.bool (a >= b), s⟩

  | op1 : Red ⟨e, s⟩ ⟨e', s'⟩
      → Red ⟨.op e o e2, s⟩ ⟨.op e' o e2, s'⟩
  | op2 : Red ⟨e2, s⟩ ⟨e2', s'⟩
      → e.IsValue → Red ⟨.op e o e2, s⟩ ⟨.op e o e2', s'⟩

  | deref : (h : s.lookup addr = some x)
      → Red ⟨.deref (addr), mtx, s⟩ ⟨.int x, mtx, s⟩
  | assign1 : (h : ∃ x, s.lookup addr = some x)
      → Red ⟨.assign addr (.int v), mtx, s⟩ ⟨.skip, mtx, s.insert addr v⟩
  | assign2 : Red ⟨e, s⟩ ⟨e', s'⟩ → Red ⟨.assign addr e, s⟩ ⟨.assign addr e', s'⟩

  | seq1: Red ⟨.seq .skip e, mtx, s⟩ ⟨e, mtx, s⟩
  | seq2: Red ⟨e1, s⟩ ⟨e1', s'⟩
      → Red ⟨.seq e1 e2, s⟩ ⟨.seq e1' e2, s'⟩

  | if_t: Red ⟨.eif (.bool true) e1 e2, s⟩ ⟨e1, s⟩
  | if_f: Red ⟨.eif (.bool false) e1 e2, s⟩ ⟨e2, s⟩

  | if_cond: Red ⟨condition, s⟩ ⟨condition', s'⟩
      → Red ⟨.eif condition e1 e2, s⟩ ⟨.eif condition' e1 e2, s'⟩

  | ewhile : Red ⟨.ewhile c body, stx⟩ ⟨.eif c (.seq body (.ewhile c body)) .skip, stx⟩

  | par1 : Red ⟨e, s⟩ ⟨e', s'⟩
      → Red ⟨.par e e2, s⟩ ⟨.par e' e2, s'⟩
  | par2 : Red ⟨e, s⟩ ⟨e', s'⟩
      → Red ⟨.par e2 e, s⟩ ⟨.par e2 e', s'⟩

  | lock : mtx.lookup nm = .some .false →
      Red ⟨.lock nm, mtx, s⟩ ⟨.skip, mtx.insert nm .true, s⟩
  | unlock : Red ⟨.unlock nm, mtx, s⟩ ⟨.skip, mtx.insert nm .false, s⟩


