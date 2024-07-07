import LeanScratch.Semantics.L1.Stx
import LeanScratch.Semantics.L1.Red


inductive Ty
  | bool
  | int
  | void

inductive TExpr: Ty → Type
  | bool (val : Bool) : TExpr .bool
  | int  (val : Int)  : TExpr .int

  | op_add (lhs : TExpr .int) (rhs : TExpr .int) : TExpr .int
  | op_gte (lhs : TExpr .int) (rhs : TExpr .int) : TExpr .bool

  | eif    (cond : TExpr .bool) (t f : TExpr a) : TExpr a
  | ewhile (cond : TExpr .bool) (e   : TExpr a) : TExpr a

  | assign (addr : String) (e : TExpr .int) : TExpr .void
  | deref (addr : String) : TExpr .int
  | seq   (a : TExpr .void) (b : TExpr v) : TExpr v
  | skip : TExpr .void

def TExpr.ty {a : Ty} (_ : TExpr a) : Ty := a

def untype : { a : Ty } → TExpr a → Expr
  | .bool, .bool v => .bool v
  | .bool, .op_gte lhs rhs => .op (untype lhs) .gte (untype rhs)

  | .int, .int v => .int v
  | .int, .op_add lhs rhs => .op (untype lhs) .add (untype rhs)
  | .int, .deref v => .deref v

  | .void, .skip => .skip
  | .void, .assign addr e => .assign addr (untype e)

  | _, .eif cond t f => .eif (untype cond) (untype t) (untype f)
  | _, .ewhile cond e => .ewhile (untype cond) (untype e)
  | _, .seq a b => .seq (untype a) (untype b)

def infer : {a : Ty} → Expr → Option (TExpr a)
  | .bool, .bool v => some $ .bool v
  | .bool, .op lhs .gte rhs => do pure $ .op_gte (← infer lhs) (← infer rhs)

  | .int, .int v => some $ .int v
  | .int, .op lhs .add rhs => do pure $ .op_add (← infer lhs) (← infer rhs)
  | .int, .deref v => some $ .deref v

  | .void, .skip => some .skip
  | .void, .assign addr e => do some $ .assign addr (← infer e)

  | _, .eif cond t f => do some $ .eif (← infer cond) (← infer t) (← infer f)
  | _, .ewhile cond e => do some $ .ewhile (← infer cond) (← infer e)
  | _, .seq a b => do some $ .seq (← infer a) (← infer b)

  | _, _ => none -- misstyped

def check (ty : Ty) (e : Expr) : Prop := (@infer ty e).isSome
def illTyped (e : Expr) : Prop := ¬ ∃ t, check t e

theorem infer_untype (a : TExpr α) : infer (untype a) = some a := by
  induction a <;> try trivial
  case op_add lhs_ih rhs_ih =>
    simp [untype, infer, lhs_ih, rhs_ih]

  case op_gte lhs_ih rhs_ih => 
    simp [untype, infer, lhs_ih, rhs_ih]

  case eif cond_ih t_ih f_ih =>
    simp [untype, infer, t_ih, f_ih, cond_ih]

  case ewhile cond_ih e_ih =>
    simp [untype, infer, cond_ih, e_ih]

  case assign e_ih =>
    simp [untype, infer, e_ih]

  case seq a_ih b_ih =>
    simp [untype, infer, a_ih, b_ih]


def TRed (pre : TExpr α) (post : TExpr β) : Red ⟨untype pre, s⟩ ⟨untype post, s'⟩ → α = β := by
  intro h
  induction pre
  <;> simp [untype] at h
  <;> try trivial
  case op_add lhs rhs lhs_ih rhs_ih => 
    sorry
    /- cases post -/
    /- <;> try { apply op_elim at h; simp at h } -/
    /- · simp [check, infer] -/
    /- case op _ o _ => -/
    /-   cases o -/
    /-   case add lhs' rhs' => -/
    /-     simp [check ] -/
    /-     induction lhs' -/
    /-     <;> try { -/
    /-       right -/
    /-       simp [illTyped] -/
    /-       intro ty -/
    /-       cases ty -/
    /-       <;> { intro h; contradiction } -/
    /-     } -/
    /-   · apply op_elim at h -/
    /-     simp at h -/

  case op_gte lhs rhs lhs_ih rhs_ih => sorry
  case eif ty cond t f cond_ih t_ih f_ih => sorry
  case assign addr e e_ih =>
    cases post
    <;> try {
      simp [untype] at h
      have x := assign_simp h
      simp at x
    }
    <;> rfl
  case deref addr =>
    cases post
    <;> try {
      simp [untype] at h
      have x := deref_simp h
      contradiction
    }
    rfl
  case seq ty a b a_ih b_ih =>
    cases post
    <;> simp [untype] at h
    <;> have x := sea_simp

    
  
  




/- def TRed (pre : TExpr α) : Red ⟨untype pre, s⟩ ⟨post, s'⟩ → check α post ∨ illTyped post := by -/
/-   intro h -/
/-   induction pre -/
/-   <;> simp [untype] at h -/
/-   <;> try trivial -/
/-   case op_add lhs rhs lhs_ih rhs_ih =>  -/
/-     cases post -/
/-     <;> try { apply op_elim at h; simp at h } -/
/-     · simp [check, infer] -/
/-     case op _ o _ => -/
/-       cases o -/
/-       case add lhs' rhs' => -/
/-         simp [check ] -/
/-         induction lhs' -/
/-         <;> try { -/
/-           right -/
/-           simp [illTyped] -/
/-           intro ty -/
/-           cases ty -/
/-           <;> { intro h; contradiction } -/
/-         } -/
/-       · apply op_elim at h -/
/-         simp at h -/

/-   case op_gte lhs rhs lhs_ih rhs_ih => sorry -/
/-   case eif ty cond t f cond_ih t_ih f_ih => sorry -/
/-   case assign addr e e_ih => -/
/-     sorry -/
/-     /- simp [check, infer] -/ -/
/-   case deref addr => -/
/-     cases post <;> try contradiction -/
/-     simp [check, infer] -/
/-   case seq ty a b a_ih b_ih => sorry -/
  
  


