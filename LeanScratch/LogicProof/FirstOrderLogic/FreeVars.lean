import LeanScratch.Vec
import LeanScratch.LogicProof.FirstOrderLogic.Formula

namespace FOL

-- At this point in my implementation I had used a (V : Type) to represent
-- variables, this let variable names be expressed clearly and with
-- [DecidableEq V] boundness could also be shown. I have decided to
-- forgo this at present as it looks like we will be doing substitution,
-- substitution is just a royal pain without De Bujin indicies. For this
-- I have now swapped and will stay like this.
--
-- Free variables are encoded as out-of-range De Bujin indicies.

-- Desicion procedures for these are trivial
inductive Term.Free (n : Nat) : Term TA → Prop
  | var : Free n (.var n)
  | const idx : Free n (path.lookup idx) → Free n (.const nm path)

def Term.vars : Term TA → List Nat
  | .var v => [v]
  | .const _ args => combine args
    where
      combine {n} : Vec _ n → List Nat
        | .nil => []
        | .cons hd tl => (vars hd) ++ combine tl

theorem Term.vars_Free {term : Term Arity} (h : n ∈ Term.vars term) : term.Free n := match term with
  | .var v => by
    simp only [vars, List.mem_singleton] at h
    subst h
    exact .var
  | .const _ args =>
    let rec x {l2} (l2 : Vec (Term Arity) l2)
      (hMem : n ∈ vars.combine l2)
      : ∃ idx, Free n (l2.lookup idx) :=
      match l2 with
      | _  %:: tl => by
        simp only [Nat.succ_eq_add_one, vars.combine, List.mem_append] at hMem
        cases hMem
        next hMem => exact ⟨.fz, vars_Free hMem⟩
        next hMem =>
          obtain ⟨idx, v⟩ := x tl hMem
          exact ⟨.fs idx, v⟩
      | .nil => by
        simp only [vars.combine, List.not_mem_nil] at hMem
    termination_by sizeOf l2
    decreasing_by
      simp_wf
      simp only [Vec.lookup]
      omega

      simp_wf
      omega
    by
    simp only [vars] at h
    obtain ⟨idx, v⟩ := x args h
    exact .const idx v
termination_by sizeOf term

theorem Term.Free_vars {term : Term Arity} (h : term.Free n) : n ∈ vars term :=
  match term with
  | .var v => by cases h; simp only [vars, List.mem_singleton]
  | .const _ tl =>
    let rec x {l idx} (l : Vec (Term Arity) l) (h' : Free n (Vec.lookup idx l)) : n ∈ vars.combine l :=
      match idx, l with
      | .fz,   _ %:: tl => by
        simp [vars.combine, Vec.lookup] at h' ⊢
        exact .inl $ Term.Free_vars h'
      | .fs v, _ %:: tl => by
        simp [vars.combine, Vec.lookup] at h' ⊢
        exact .inr $ x tl h'
    by
    cases h; next idx v =>
    simp only [vars]
    exact x tl v

inductive Formula.Free : Nat → Formula TA PA → Prop
  | pred idx : (app.lookup idx).Free n → Free n (.pred n app)

  | neg   : Free n v → Free n v.neg

  | conjl : Free n v → Free n (.conj v x)
  | conjr : Free n v → Free n (.conj x v)
  | disjl : Free n v → Free n (.disj v x)
  | disjr : Free n v → Free n (.disj x v)
  | impl  : Free n v → Free n (.imp v x)
  | impr  : Free n v → Free n (.imp x v)
  | iffl  : Free n v → Free n (.iff v x)
  | iffr  : Free n v → Free n (.iff x v)

  | exis : Free n.succ v → Free n (.exis v)
  | univ : Free n.succ v → Free n (.univ v)

