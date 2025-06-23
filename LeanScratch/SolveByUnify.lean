import Lean.Elab
import Lean.Elab.Tactic
import Lean.Environment

def getPrincipleFunctor : Lean.Expr → Option Lean.Name
  | .proj _ _ _
  | .mdata _ _
  | .lit _
  | .letE _ _ _ _ _
  | .forallE _ _ _ _
  | .lam _ _ _ _
  | .sort _
  | .mvar (Lean.MVarId.mk _)
  | .fvar (Lean.FVarId.mk _)
  | .bvar _ => none
  | .const dname _ => some dname
  | .app l _ => getPrincipleFunctor l

elab "sunify" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let goalType ← Lean.Elab.Tactic.getMainTarget
  let .some pf := getPrincipleFunctor goalType | throwError "no principle functor"
  let ctx ← Lean.getEnv
  dbg_trace f!"goal type: {pf}"
  return

namespace Test

inductive Len : List α → Nat → Prop
  | nil : Len [] 0
  | cons : Len t n → Len (hd :: t) n.succ

example (h : Len tl n) : Len ([a, b, c] ++ tl) (n + 3) := by
  sunify

inductive Append : List α → List α → List α → Prop
  | anil  : Append [] a a
  | acons : Append t a r → Append (h :: t) a (h :: r)

inductive Mem : α → List α → Prop
  | ahead : Mem h (h :: t)
  | atl  : Mem a tl → Mem a (_h :: tl)

def Mem' (a : α) (ls : List α) : Prop := ∃ l1 l2, Append l1 (a :: l2) ls

example : Mem a ls = Mem' a ls := by
  induction ls
  · ext; constructor
    · rintro (_|_)
    · rintro ⟨l1, l2, (_|_)⟩
  case cons tail ih =>
    ext; constructor
    · rintro (_|nx)
      · exact ⟨[], tail, .anil⟩
      · rw [ih] at nx
        rcases nx with ⟨l1, l2, h⟩
        exact ⟨_ :: l1, l2, .acons h⟩
    · rintro ⟨l1, l2, (_|nx)⟩
      · exact .ahead
      · have nx : Mem' a tail := ⟨_, _, nx⟩
        rw [←ih] at nx
        exact .atl nx
