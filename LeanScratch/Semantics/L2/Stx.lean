import Mathlib.Data.Rel
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith.Frontend

namespace L2

@[aesop safe [constructors, cases]]
inductive Ty
  | bool
  | int
  | void
  | arrow (arg res : Ty)
deriving DecidableEq

@[aesop safe [constructors, cases]]
inductive Op
  | add
  | gte
deriving DecidableEq

@[aesop safe [constructors, cases]]
inductive Expr
  | bool (val : Bool)
  | int  (val : Int)
  | skip

  | op (lhs : Expr) (op : Op) (rhs : Expr)

  | eif    (cond t f : Expr)
  | ewhile (cond e   : Expr)

  | assign (addr : String) (e : Expr)
  | deref (addr : String)

  | seq   (a b : Expr)

  | ref (name : String)
  | abs (name : String) (ty : Ty) (body : Expr)
  | app (fn arg : Expr) ---------> inference is decidable this is not needed
                        -- FUN!: Implement unification and make this nicer
deriving DecidableEq

-- scary, dont know how to prove this is correct
def Expr.subst (base : Expr) (name : String) (repl : Expr) : Expr := match base with
  | bool v => .bool v
  | int v  => .int v
  | skip   => .skip

  | op lhs o rhs => .op (lhs.subst name repl) o (rhs.subst name repl)

  | eif cond t f => .eif (cond.subst name repl) (t.subst name repl) (f.subst name repl)
  | ewhile c body => .ewhile (c.subst name repl) (body.subst name repl)

  | assign addr e => .assign addr (e.subst name repl)
  | deref addr => .deref addr

  | seq a b => .seq (a.subst name repl) (b.subst name repl)

  | ref name' =>
    if name = name' then repl
    else .ref name'

  | abs name' ty body =>
    if name = name' then .abs name' ty body
    else .abs name' ty (body.subst name repl)

  | app fn arg => .app (fn.subst name repl) (arg.subst name repl)

abbrev Expr.isInt : Expr → Bool
  | .int _ => true
  | _ => false

theorem isInt_defn {e : Expr} : (∃ i, e = .int i) ↔ e.isInt := by
  constructor
  <;> intro h
  · rcases h with ⟨_, h⟩
    rw [h]
  · cases e
    <;> simp [Expr.isInt] at h
    case int v =>
      use v

abbrev Expr.isValue: Expr → Bool
  | .bool _ | .int _ | .skip => true
  | _ => false

abbrev Expr.isFnValue: Expr → Bool
  | .bool _ | .int _ | .skip | .abs _ _ _ => true
  | _ => false

/- -- could be defined as a set -/
/- @[aesop safe [constructors, cases]] -/
/- inductive Expr.fv : Expr → String → Prop -/
/-   | seql : a.fv s → Expr.fv (.seq a b) s -/
/-   | seqr : b.fv s → Expr.fv (.seq a b) s -/

/-   | opl : a.fv s → Expr.fv (.op a o b) s -/
/-   | opr : b.fv s → Expr.fv (.op a o b) s -/

/-   | ewhilecond : c.fv s → Expr.fv (.ewhile c b) s -/
/-   | ewhilebody : b.fv s → Expr.fv (.ewhile c b) s -/

/-   | appl : a.fv s → Expr.fv (.app a b) s -/
/-   | appr : b.fv s → Expr.fv (.app a b) s -/

/-   | ifc : c.fv s → Expr.fv (.eif c t f) s -/
/-   | ift : t.fv s → Expr.fv (.eif c t f) s -/
/-   | iff : f.fv s → Expr.fv (.eif c t f) s -/

/-   | assign : e.fv s → Expr.fv (.assign n e) s -/
/-   | abs : b.fv s → s ≠ name → Expr.fv (.abs name ty b) s -/

/-   | ref : Expr.fv (.ref nm) nm -/

/- @[aesop safe [constructors, cases]] -/
/- inductive Expr.bv : Expr → String → Prop -/
/-   | seql : a.bv s → Expr.bv (.seq a b) s -/
/-   | seqr : b.bv s → Expr.bv (.seq a b) s -/

/-   | opl : a.bv s → Expr.bv (.op a o b) s -/
/-   | opr : b.bv s → Expr.bv (.op a o b) s -/

/-   | ewhilecond : c.bv s → Expr.bv (.ewhile c b) s -/
/-   | ewhilebody : b.bv s → Expr.bv (.ewhile c b) s -/

/-   | appl : a.bv s → Expr.bv (.app a b) s -/
/-   | appr : b.bv s → Expr.bv (.app a b) s -/

/-   | ifc : c.bv s → Expr.bv (.eif c t f) s -/
/-   | ift : t.bv s → Expr.bv (.eif c t f) s -/
/-   | iff : f.bv s → Expr.bv (.eif c t f) s -/

/-   | assign : e.bv s → Expr.bv (.assign n e) s -/
/-   | abs : Expr.bv (.abs name ty b) name -/


def Expr.v : Expr → Finset String 
  | .bool _ | .int _ | .skip | .deref _ => {}
  | .seq a b | .op a _ b | .ewhile a b | .app a b => a.v ∪ b.v
  | .assign _ a => a.v
  | .eif c t f  => c.v ∪ t.v ∪ f.v
  | .abs name _ b => b.v ∪ { name }
  | .ref nm => { nm }

def Expr.fv : Expr → Finset String
  | .bool _ | .int _ | .skip | .deref _ => {}
  | .seq a b | .op a _ b | .ewhile a b | .app a b => a.fv ∪ b.fv
  | .assign _ a => a.fv
  | .eif c t f  => c.fv ∪ t.fv ∪ f.fv
  | .abs name _ b => b.fv \ { name }
  | .ref nm => { nm }

def Expr.bv : Expr → Finset String
  | .bool _ | .int _ | .ref _ | .skip | .deref _ => {}
  | .seq a b | .op a _ b | .ewhile a b | .app a b => a.bv ∪ b.bv
  | .assign _ a => a.bv
  | .eif c t f  => c.bv ∪ t.bv ∪ f.bv
  | .abs name _ b => b.bv ∪ { name }

def Expr.mkFreshV : Expr → String
  | .bool _ | .int _ | .skip | .deref _ => ""
  | .seq a b | .op a _ b | .ewhile a b | .app a b => (Expr.mkFreshV a) ++ (Expr.mkFreshV b)
  | .assign _ a => a.mkFreshV
  | .eif c t f  => c.mkFreshV ++ t.mkFreshV ++ f.mkFreshV ++ "x"
  | .abs name _ b => b.mkFreshV ++ name ++ "x"
  | .ref nm => nm ++ "x"

section
variable {e : Expr}

open Finset in
theorem fv_union_bv_eq_v : e.bv ∪ e.fv = e.v := by
  induction e
  <;> simp_all only [Expr.bv, Expr.fv, union_idempotent, Expr.v, union_assoc, union_sdiff_self_eq_union, empty_union]
  case op l _ r l_ih r_ih =>
    calc
      l.bv ∪ (r.bv ∪ (l.fv ∪ r.fv)) = l.bv ∪ ((l.fv ∪ r.fv) ∪ r.bv) := by rw [union_comm r.bv]
      _ = (l.bv ∪ l.fv) ∪ (r.fv ∪ r.bv)                             := by repeat rw [union_assoc]
      _ = l.v ∪ r.v                                                 := by rw [l_ih, union_comm r.fv, r_ih]

  case eif c t f c_ih t_ih f_ih =>
    calc
      c.bv ∪ (t.bv ∪ (f.bv ∪ (c.fv ∪ (t.fv ∪ f.fv)))) =
        c.bv ∪ (t.bv ∪ ((c.fv ∪ (t.fv ∪ f.fv)) ∪ f.bv))   := by rw [union_comm f.bv]
      _ = c.bv ∪ (((c.fv ∪ (t.fv ∪ f.fv)) ∪ f.bv) ∪ t.bv) := by rw [union_comm t.bv]
      _ = c.bv ∪ c.fv ∪ t.fv ∪ f.fv ∪ f.bv ∪ t.bv         := by simp only [union_assoc]
      _ = c.v ∪ t.fv ∪ ((f.fv ∪ f.bv) ∪ t.bv)             := by simp only [union_assoc, c_ih]
      _ = c.v ∪ t.fv ∪ (f.v ∪ t.bv)                       := by rw [union_comm f.fv, f_ih]
      _ = c.v ∪ t.fv ∪ (t.bv ∪ f.v)                       := by rw [union_comm f.v]
      _ = c.v ∪ (t.fv ∪ t.bv) ∪ f.v                       := by simp only [union_assoc]
      _ = c.v ∪ t.v ∪ f.v                                 := by rw [union_comm t.fv, t_ih]
      _ = c.v ∪ (t.v ∪ f.v)                               := by simp only [union_assoc]

  case ewhile c e c_ih e_ih => 
    calc
      c.bv ∪ (e.bv ∪ (c.fv ∪ e.fv)) = c.bv ∪ ((c.fv ∪ e.fv) ∪ e.bv) := by rw [union_comm e.bv]
      _ = (c.bv ∪ c.fv) ∪ (e.fv ∪ e.bv)                             := by repeat rw [union_assoc]
      _ = c.v ∪ e.v                                                 := by rw [c_ih, union_comm e.fv, e_ih]

  case seq a b a_ih b_ih =>
    calc
      a.bv ∪ (b.bv ∪ (a.fv ∪ b.fv)) = a.bv ∪ ((a.fv ∪ b.fv) ∪ b.bv) := by rw [union_comm b.bv]
      _ = (a.bv ∪ a.fv) ∪ (b.fv ∪ b.bv)                             := by repeat rw [union_assoc]
      _ = a.v ∪ b.v                                                 := by rw [a_ih, union_comm b.fv, b_ih]
  case abs n _ b b_ih =>
    calc
      b.bv ∪ ({n} ∪ b.fv) = b.bv ∪ (b.fv ∪ {n}) := by rw [union_comm b.fv]
      _ = (b.bv ∪ b.fv) ∪ {n} := by rw [union_assoc]
      _ = (b.v) ∪ {n} := by rw [b_ih]

  case app f a fn_ih arg_ih =>
    calc
      f.bv ∪ (a.bv ∪ (f.fv ∪ a.fv)) = f.bv ∪ ((f.fv ∪ a.fv) ∪ a.bv) := by rw [union_comm a.bv]
      _ = (f.bv ∪ f.fv) ∪ (a.fv ∪ a.bv)                             := by repeat rw [union_assoc]
      _ = f.v ∪ a.v                                                 := by rw [fn_ih, union_comm a.fv,arg_ih]

theorem Expr.mkFreshV_longer_than_all_vs : ∀ s ∈ e.v, s.length < e.mkFreshV.length := by
  intro a h
  induction e generalizing a
  <;> simp_all [Expr.v, Expr.mkFreshV, String.length]
  <;> (try {
    rename_i a b
    cases h
    next h =>
      have := a _ h
      linarith
    next h =>
      have := b _ h
      linarith
  })
  case eif cond t f =>
    cases h
    next h =>
      have := cond a h
      linarith
    next h =>
    cases h
    next h =>
      have := t a h
      linarith
    next h =>
      have := f a h
      linarith

  case abs body =>
    cases h
    next h =>
      have := body _ h
      linarith
    next h =>
      simp [h]
      linarith

theorem Expr.mkFreshV_longer_than_all_fvs : ∀ s ∈ e.fv, s.length < e.mkFreshV.length := by
  intro a h
  induction e generalizing a
  <;> simp_all [Expr.bv, Expr.fv, Expr.mkFreshV, String.length]
  <;> (try {
    rename_i a b
    cases h
    next h =>
      have := a _ h
      linarith
    next h =>
      have := b _ h
      linarith
  })
  case eif cond t f =>
    cases h
    next h =>
      have := cond a h
      linarith
    next h =>
    cases h
    next h =>
      have := t a h
      linarith
    next h =>
      have := f a h
      linarith

  case abs body =>
    have := body _ h.1
    linarith

theorem Expr.mkFreshV_longer_than_all_bvs : ∀ s ∈ e.bv, s.length < e.mkFreshV.length := by
  intro a h
  induction e
  <;> simp_all [Expr.bv, Expr.fv, Expr.mkFreshV, String.length]
  <;> (try {
    rename_i a b
    cases h
    next h =>
      have := a h
      linarith
    next h =>
      have := b h
      linarith
  })
  case eif cond t f =>
    cases h
    next h =>
      have := cond h
      linarith
    next h =>
    cases h
    next h =>
      have := t h
      linarith
    next h =>
      have := f h
      linarith

  case abs body =>
    cases h
    next h =>
      have := body h
      linarith
    next h =>
      simp only [String.length, h, ↓Char.isValue, List.length_singleton]
      linarith

theorem Expr.mkFreshV_nin_bv : e.mkFreshV ∉ e.bv := by
  by_contra!
  have := Expr.mkFreshV_longer_than_all_bvs e.mkFreshV this
  simp only [lt_self_iff_false] at this

theorem Expr.mkFreshV_nin_fv : e.mkFreshV ∉ e.fv := by
  by_contra!
  have := Expr.mkFreshV_longer_than_all_fvs e.mkFreshV this
  simp only [lt_self_iff_false] at this

theorem bv_disjoint_fv : Disjoint e.bv e.fv := by
  induction e
  <;> simp_all [Disjoint, Expr.bv, Expr.fv, Finset.inter_self, Finset.not_mem_empty, not_false_eq_true, Finset.inter_singleton_of_not_mem, Finset.union_assoc]
  <;> intro h a b
  case op lhs op rhs lhs_ih rhs_ih => sorry
  case eif cont t f cont_ih t_ih f_ih => sorry
  case ewhile cond e cond_ih e_ih => sorry
  case seq a b a_ih b_ih => sorry
  case abs name ty body body_ih => sorry
  case app fn arg fn_ih arg_ih => sorry

end

def Expr.α (prev : String) (repl : String) : Expr → Expr
  | .seq a b => .seq (a.α prev repl) (b.α prev repl)
  | .op a o b => .op (a.α prev repl) o (b.α prev repl)
  | .ewhile cond body => .ewhile (cond.α prev repl) (body.α prev repl)
  | .app a b => .app (a.α prev repl) (b.α prev repl)
  | .assign name v => .assign name (v.α prev repl)
  | .eif cond t f => .eif (cond.α prev repl) (t.α prev repl) (f.α prev repl)
  | .abs name ty e => .abs name ty (if name = prev then e else e.α prev repl)
  | .ref name => .ref (if name = prev then repl else name)
  | v => v

end L2

