import LeanScratch.Semantics.L2.Stx
import Mathlib.Data.Rel
import Mathlib.Data.List.AList
import LeanScratch.Relation

namespace L2

abbrev VarMap := AList (fun _ : String => Int)

abbrev State := Expr × VarMap

inductive Red : State → State → Prop
  | op_add (a b : Int) : Red ⟨.op (.int a) .add (.int b), s⟩ ⟨.int (a + b), s⟩
  | op_gte (a b : Int) : Red ⟨.op (.int a) .gte (.int b), s⟩ ⟨.bool (a >= b), s⟩

  | op1 : Red ⟨e, s⟩ ⟨e', s'⟩
      → Red ⟨.op e o e2, s⟩ ⟨.op e' o e2, s'⟩
  | op2 : Red ⟨e2, s⟩ ⟨e2', s'⟩
      → e.IsValue → Red ⟨.op e o e2, s⟩ ⟨.op e o e2', s'⟩

  | deref : (h : s.lookup addr = some x)
      → Red ⟨.deref addr, s⟩ ⟨.int x, s⟩
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
  -- TODO: add this
  /- | letrecfn : -/
  /-       Red ⟨.letRecVal (.arrow t1 t2) (.abs t1 e1) e2, s⟩ ⟨e2.β (.abs) , s⟩ -/

/- theorem red_det : Red i o₁ ∧ Red i o₂ → o₁ = o₂ := by -/
/-   intro ⟨ha, hb⟩ -/
/-   induction ha generalizing o₂ -/
/-   <;> cases hb -/
/-   <;> try trivial -/

/-   case op1.op2 epre spre e₁ s₁ op eprealt ha a_ih e₂ s₂ epre_is_int hb =>  -/
/-     rw [p] at ha -/
/-     contradiction -/

/-   case op2.op1 epre spre e₁ s₁ e op ha e_is_int a_ih e₂ s₂ hb => -/
/-     have ⟨_, p⟩ := isInt_defn.mpr e_is_int -/
/-     rw [p] at hb -/
/-     contradiction -/

/-   case op1.op1 epre spre e₁ s₁ o e2 ha a_ih e₂ s₂ hb => -/
/-     injection a_ih hb with eq₁ eq₂ -/
/-     rw [eq₁, eq₂] -/
/-   case op2.op2 epre spre e₁ s₁ _ op ha epre_is_int a_ih e₂ s₂ _ hb => -/
/-     injection a_ih hb with eq₁ eq₂ -/
/-     rw [eq₁, eq₂] -/

/-   case deref.deref h₁ _ h₂=> -/
/-     injection h₁.symm.trans h₂ with eq₁ -/
/-     rw [eq₁] -/

/-   case assign2.assign2 epre spre e₁ s₁ addr ha a_ih e₂ s₂ hb => -/
/-     injection a_ih hb with eq₁ eq₂ -/
/-     rw [eq₁, eq₂] -/

/-   case seq2.seq2 epre spre e₁ s₁ erhs ha a_ih e₂ s₂ hb => -/
/-     injection a_ih hb with eq₁ eq₂ -/
/-     rw [eq₁, eq₂] -/

/-   case if_cond.if_cond condpre spre cond₁ s₁ e1 e2 ha a_ih cond₂ s₂ hb =>  -/
/-     injection a_ih hb with eq₁ eq₂ -/
/-     rw [eq₁, eq₂] -/

/-   case beta.app2 x name body repl s replVal _ _ _ a  => -/
/-     cases repl -/
/-     <;> simp only at replVal -/
/-     <;> cases a -/
/-   case app1.app1 e s e₁ s₁ e₂ s₂ a_ih e₁' s₁' a => -/
/-     injection a_ih a with eq₁ eq₂ -/
/-     rw [eq₁, eq₂] -/
/-   case app1.app2 e _ _ _ _ a _ _ _ v _ => -/
/-     cases e -/
/-     <;> simp only at v -/
/-     <;> cases a -/

/-   case app2.beta e _ _ _ a _ _ _ _ _ v => -/
/-     cases e -/
/-     <;> simp only at v -/
/-     <;> cases a -/

/-   case app2.app1 e v _ _ _ _ a => -/
/-     cases e -/
/-     <;> simp only at v -/
/-     <;> cases a -/
/-   case app2.app2 e s e₁ s₁ e' e'v _ a_ih _ _ _ a => -/
/-     injection a_ih a with eq₁ eq₂ -/
/-     rw [eq₁, eq₂] -/

/- end L2 -/

