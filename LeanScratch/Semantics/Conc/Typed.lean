import LeanScratch.Semantics.Conc.Stx
import LeanScratch.Relation
import Mathlib.Data.List.AList

namespace L1Par

inductive Ty
  | bool
  | int
  | void
  | proc
deriving DecidableEq

-- TODO: Change Int to Unit
abbrev Ctx := AList fun _ : String => Int

inductive TTySpec : Ctx → TExpr → Ty → Prop
  | bool : TTySpec _ (.bool b) .bool
  | int  : TTySpec _ (.int i)  .int
  | skip : TTySpec _ .skip     .void

  | op_add : TTySpec ctx a .int → TTySpec ctx b .int
      → TTySpec ctx (.op a .add b) .int
  | op_gte : TTySpec ctx a .int → TTySpec ctx b .int
      → TTySpec ctx (.op a .gte b) .bool

  | deref : (h : ∃ w, ctx.lookup addr = some w)
      → TTySpec ctx (.deref addr) .int
  | assign : (h : ∃ w, ctx.lookup addr = some w) → TTySpec ctx e .int
      → TTySpec ctx (.assign addr e) .void
  | seq : TTySpec ctx a .void → TTySpec ctx b o
      → TTySpec ctx (.seq a b) o

  | eif : TTySpec ctx c .bool → TTySpec ctx t a → TTySpec ctx f a
      → TTySpec ctx (.eif c t f) a

  | ewhile : TTySpec ctx c .bool → TTySpec ctx body .void
      → TTySpec ctx (.ewhile c body) .void

  | lock   (h : ∃ w, ctx.lookup addr = some w) :
        TTySpec ctx (.lock   addr) .void
  | unlock   (h : ∃ w, ctx.lookup addr = some w) :
        TTySpec ctx (.unlock addr) .void

theorem NonProc : ¬TTySpec ctx e .proc := fun h =>
  match e with
  | .bool _
  | .int _
  | .skip
  | .op _ _ _
  | .deref _
  | .assign _ _
  | .lock _
  | .unlock _ => by cases h
  | .seq _ v   => match h with | .seq _ h   => NonProc h
  | .eif _ v _ => match h with | .eif _ h _ => NonProc h

inductive TySpec : Ctx → Expr → Ty → Prop
  | tex : TTySpec ctx e .void → TySpec ctx (.tex e) .proc
  | parallel : TySpec ctx a .proc →
               TySpec ctx b .proc
      → TySpec ctx (.par a b) .proc

