import Lean.Elab.Term
import Lean.Server.InfoUtils
/- inductive  -/

open Lean Elab Elab.Term

syntax (name := pit) "pinftree" term : term
/- syntax (name := pit) "⟨⟨" term,* "⟩⟩" : term -/

#check Syntax

def extractArgsAndNm : Expr → Option (Name × List Expr)
  | .const nm _ => .some ⟨nm, []⟩
  | .app a b => do
    let ⟨nm, ls⟩ ← extractArgsAndNm a
    return ⟨nm, b :: ls⟩
  | _ => .none


partial def buildInfTree (e : Expr) : MetaM String := do
  match extractArgsAndNm e with
  | .some (nm, ls) => 
    let env ← getEnv
    match env.find? (nm ++ `pitHandle) with
    | .some (.defnInfo v) => throwError "custom handler"
    | _ =>
      let exprs ← ls.mapM buildInfTree
      let joinedV := String.intercalate " " exprs
      return s!"\\infer[{nm}] \x7bTYPE\x7d \x7b{joinedV}\x7d"
      /- throwError "base handler" -/
  | .none =>
    match e with
    | .lam _ _ _ _ => throwError "lam"
    | e =>
      dbg_trace "Unexpected expr type {e} ({repr e})"
      return ""
    

/- elab "pinftree" x:term typ? : term => do -/
@[term_elab pit]
def myanonImpl : TermElab := fun stx typ? => do
  tryPostponeIfNoneOrMVar typ?
  -- If we haven't found the type after postponing just error
  let some typ := typ? | throwError "expected type must be known"

  let .node _ _ #[_, stx] := stx | throwError "Stx failed to match {repr stx}"

  let expr : Expr ← elabTerm stx $ .some typ

  throwErrorAt stx (←buildInfTree expr)

  return expr


example : List Nat :=
  pinftree Nat.zero :: ([] : List Nat)

