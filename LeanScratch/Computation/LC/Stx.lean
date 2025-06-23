namespace LC

@[pp_nodot]
inductive Stx
  | bvar (id : Nat)
  | app  (fn arg : Stx)
  | abs  (body : Stx)
deriving DecidableEq

declare_syntax_cat stx_dbIdx

syntax stx_dbIdx stx_dbIdx : stx_dbIdx
syntax num : stx_dbIdx
syntax ident : stx_dbIdx
syntax "!(" term ")" : stx_dbIdx
syntax "(" stx_dbIdx ")" : stx_dbIdx
syntax "λ" ident* "." stx_dbIdx : stx_dbIdx

syntax "[l" num ident* "|" stx_dbIdx "]" : term
syntax "[l|" stx_dbIdx "]" : term

open Lean in
instance : HAdd NumLit Nat NumLit where
  hAdd x n := Syntax.mkNumLit s!"{x.getNat + n}"

macro_rules
  | `([l $_t $_ids*| $v:num ]) => `(Stx.bvar $v)
  | `([l $_t | $v:ident ]) => `($v)
  | `([l $_t | !($t) ]) => `($t)
  | `([l $t $h $ids*| $v:ident ]) =>
    if h.getId = v.getId then `(Stx.bvar $t)
    else `([l $(t + 1) $ids* | $v:ident])
  | `([l $t $ids*| ($v) ]) => `(([l $t $ids* |$v]))
  | `([l $t $ids*| λ. $v]) => `(Stx.abs ([l $(t + 1) $ids*|$v]))
  | `([l $t $ids*| λ $i. $v]) => `(Stx.abs ([l $t $i $ids*|$v]))
  | `([l $t $ids*| λ $i $is*. $v]) => `(Stx.abs ([l $t $i $ids*| λ $is*. $v]))
  | `([l $t $ids*| $a $b]) => `(Stx.app ([l $t $ids* |$a]) ([l $t $ids*|$b]))
  | `([l| $v]) => `([l 0 | $v])

open Lean in
def Stx.uex_inner : Syntax.Term → PrettyPrinter.UnexpandM (TSyntax `stx_dbIdx)
  | `($i:ident) => `(stx_dbIdx|$i:ident)
  | `([l|$b]) => `(stx_dbIdx|$b)
  | `($t) =>`(stx_dbIdx|!($t))

@[app_unexpander Stx.bvar]
def Stx.bvar.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $num:num) => `([l| $num:num])
  | _ => throw ()

@[app_unexpander Stx.abs]
def Stx.abs.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $v) => do `([l| λ. $(← uex_inner v)])
  | _ => throw ()

@[app_unexpander Stx.app]
def Stx.app.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $a $b) => do
    let a ← uex_inner a
    let b ← uex_inner b
    let perenify : Lean.TSyntax `stx_dbIdx → Lean.PrettyPrinter.UnexpandM (Lean.TSyntax `stx_dbIdx)
      | `(stx_dbIdx|λ. $b) => `(stx_dbIdx|(λ. $b))
      | `(stx_dbIdx|$a $b) => `(stx_dbIdx|($a $b))
      | v => `(stx_dbIdx|$v)
    let a ← perenify a
    let b ← perenify b
    `([l| $a $b])
  | _ => throw ()
