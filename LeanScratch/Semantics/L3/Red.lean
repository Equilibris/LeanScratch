import LeanScratch.Semantics.L3.Stx

namespace L3

abbrev VarMap := List Expr

abbrev State := Expr × VarMap

def change (v : α) : ℕ → List α → List α
  | 0,    _ :: tl =>  v :: tl
  | n+1, hd :: tl => hd :: (change v n tl)
  | _, [] => []

inductive Red : State → State → Prop
  | op_add (a b : Int) : Red ⟨.op (.int a) .add (.int b), s⟩ ⟨.int (a + b), s⟩
  | op_gte (a b : Int) : Red ⟨.op (.int a) .gte (.int b), s⟩ ⟨.bool (a >= b), s⟩

  | op1 : Red ⟨e, s⟩ ⟨e', s'⟩
      → Red ⟨.op e o e2, s⟩ ⟨.op e' o e2, s'⟩
  | op2 : Red ⟨e2, s⟩ ⟨e2', s'⟩
      → e.IsValue → Red ⟨.op e o e2, s⟩ ⟨.op e o e2', s'⟩

  | seq1 : Red ⟨.seq .skip e, s⟩ ⟨e, s⟩
  | seq2 : Red ⟨e1, s⟩ ⟨e1', s'⟩
      → Red ⟨.seq e1 e2, s⟩ ⟨.seq e1' e2, s'⟩

  | if_t : Red ⟨.eif (.bool true) e1 e2, s⟩ ⟨e1, s⟩
  | if_f : Red ⟨.eif (.bool false) e1 e2, s⟩ ⟨e2, s⟩

  | if_cond : Red ⟨condition, s⟩ ⟨condition', s'⟩
      → Red ⟨.eif condition e1 e2, s⟩ ⟨.eif condition' e1 e2, s'⟩

  | ewhile : Red ⟨.ewhile c body, stx⟩ ⟨.eif c (.seq body (.ewhile c body)) .skip, stx⟩

  | app1 : Red ⟨e1, s⟩ ⟨e1', s'⟩
      → Red ⟨.app e1 e2, s⟩ ⟨.app e1' e2, s'⟩
  | app2 : e1.IsValue → Red ⟨e2, s⟩ ⟨e2', s'⟩
      → Red ⟨.app e1 e2, s⟩ ⟨.app e1 e2', s'⟩
  | fn : repl.IsValue
      → Red ⟨.app (.abs t body) repl, s⟩ ⟨body.β repl, s⟩

  | let1 : Red ⟨e1, s1⟩ ⟨e2, s2⟩
      → Red ⟨.letVal t e1 e, s1⟩ ⟨.letVal t e2 e, s2⟩
  | let2 : e1.IsValue
      → Red ⟨.letVal t e1 e, s1⟩ ⟨e.β e1, s1⟩

  | pair1 : Red ⟨a, s⟩ ⟨a', s'⟩
      → Red ⟨.pair a b, s⟩ ⟨.pair a' b, s'⟩
  | pair2 : a.IsValue → Red ⟨b, s⟩ ⟨b', s'⟩
      → Red ⟨.pair a b, s⟩ ⟨.pair a b', s'⟩

  | fst1 : Red ⟨a, s⟩ ⟨a', s'⟩
      → Red ⟨.fst a, s⟩ ⟨.fst a', s'⟩
  | fst2 : a.IsValue → b.IsValue
      → Red ⟨.fst $ .pair a b, s⟩ ⟨a, s'⟩

  | snd1 : Red ⟨a, s⟩ ⟨a', s'⟩
      → Red ⟨.snd a, s⟩ ⟨.snd a', s'⟩
  | snd2 : a.IsValue → b.IsValue
      → Red ⟨.snd $ .pair a b, s⟩ ⟨b, s'⟩

  | inl : Red ⟨a, s⟩ ⟨a', s'⟩
      → Red ⟨.inl t a, s⟩ ⟨.inl t a', s'⟩
  | inr : Red ⟨a, s⟩ ⟨a', s'⟩
      → Red ⟨.inr t a, s⟩ ⟨.inr t a', s'⟩

  | case_scrutinee : Red ⟨scrutinee, s⟩ ⟨scrutinee', s'⟩
      → Red ⟨.case scrutinee a b, s⟩ ⟨.case scrutinee' a b, s'⟩
  | case_inl : scrutinee.IsValue
      → Red ⟨.case (.inl t scrutinee) a b, s⟩ ⟨a.β scrutinee, s⟩
  | case_inr : scrutinee.IsValue
      → Red ⟨.case (.inr t scrutinee) a b, s⟩ ⟨b.β scrutinee, s⟩

  | ref1 : Red ⟨e, s⟩ ⟨e', s'⟩
      → Red ⟨.ref t e, s⟩ ⟨.ref t e', s'⟩
  | ref2 : e.IsValue
      → Red ⟨.ref t e, s⟩ ⟨.loc t s.length, s ++ [e]⟩

  | assign_lhs : Red ⟨e, s⟩ ⟨e', s'⟩
      → Red ⟨.assign e rhs, s⟩ ⟨.assign e' rhs, s'⟩
  | assign_rhs : lhs.IsValue → Red ⟨e, s⟩ ⟨e', s'⟩
      → Red ⟨.assign lhs e, s⟩ ⟨.assign lhs e', s'⟩
  | assign_op : rhs.IsValue
      → Red ⟨.assign (.loc _ pos) rhs, s⟩ ⟨.skip, change rhs pos s⟩

