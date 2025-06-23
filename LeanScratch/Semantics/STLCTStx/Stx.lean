import LeanScratch.Fin2

namespace STLCTS

@[pp_nodot]
inductive Ty
  | direct (id : ℕ)   -- a unique type
  | arr (fn arg : Ty) -- a function type
deriving DecidableEq

@[pp_nodot]
inductive Stx : List Ty → Type
  | bvar (id : Fin2 ls.length) : Stx ls
  | app  (fn arg : Stx ls) : Stx ls
  | abs  (ty : Ty) (body : Stx (ty :: tl)) : Stx tl
deriving DecidableEq

open Lean in
instance : HAdd NumLit Nat NumLit where
  hAdd x n := Syntax.mkNumLit s!"{x.getNat + n}"

declare_syntax_cat tstlc_stx_dbIdx

syntax ident : tstlc_stx_dbIdx
syntax num : tstlc_stx_dbIdx
syntax tstlc_stx_dbIdx "->" tstlc_stx_dbIdx : tstlc_stx_dbIdx
syntax tstlc_stx_dbIdx "→" tstlc_stx_dbIdx : tstlc_stx_dbIdx
syntax "!(" term ")" : tstlc_stx_dbIdx
syntax "(" tstlc_stx_dbIdx ")" : tstlc_stx_dbIdx

syntax "[tyl" "|" tstlc_stx_dbIdx "]" : term

macro_rules
  | `([tyl| $v:num ]) => `(Ty.direct $v)
  | `([tyl| $v:ident ]) => `($v)
  | `([tyl| $a →  $b ]) => `(Ty.arr [tyl|$a] [tyl|$b])
  | `([tyl| $a -> $b ]) => `(Ty.arr [tyl|$a] [tyl|$b])
  | `([tyl| !($t) ]) => `($t)
  | `([tyl| ($t) ]) => `(([tyl|$t]))

open Lean in
def Ty.uex_inner : Syntax.Term → PrettyPrinter.UnexpandM (TSyntax `tstlc_stx_dbIdx)
  | `($i:ident) => `(tstlc_stx_dbIdx|$i:ident)
  | `([tyl|$b]) => `(tstlc_stx_dbIdx|$b)
  | `($t) =>`(tstlc_stx_dbIdx|!($t))

@[app_unexpander Ty.direct]
def Ty.direct.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $num:num) => `([tyl| $num:num])
  | _ => throw ()

@[app_unexpander Ty.arr]
def Ty.arr.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $a $b) => do
    match ←Ty.uex_inner a with
    | a@`(tstlc_stx_dbIdx|$_ → $_) => `([tyl| ($a)  →  $(←Ty.uex_inner b)])
    | a => `([tyl| $a  →  $(←Ty.uex_inner b)])
  | _ => throw ()

declare_syntax_cat stlc_stx_dbIdx

set_option pp.fieldNotation false in

syntax stlc_stx_dbIdx stlc_stx_dbIdx : stlc_stx_dbIdx
syntax num : stlc_stx_dbIdx
syntax ident : stlc_stx_dbIdx
syntax "!(" term ")" : stlc_stx_dbIdx
syntax "(" stlc_stx_dbIdx ")" : stlc_stx_dbIdx
syntax "λ" (ident)? ":" tstlc_stx_dbIdx "." stlc_stx_dbIdx : stlc_stx_dbIdx

syntax "[tl" num ident* "|" stlc_stx_dbIdx "]" : term
syntax "[tl|" stlc_stx_dbIdx "]" : term

open Lean in
def Lean.NumLit.toFin2 (lit : NumLit) : MacroM Term := body lit.getNat
  where
    body : _ → _
      | 0 => `(Fin2.fz)
      | n+1 => do `(Fin2.fs $(←body n))

partial def Fin2Term.toNat : Lean.Term → Lean.PrettyPrinter.UnexpandM Nat
  | `($i:ident) =>
    if i.getId = ``Fin2.fz then return 0
    else throw ()
  | `($fname:ident $b) =>
    if fname.getId = ``Fin2.fs then return Nat.succ $ ←(Fin2Term.toNat b)
    else throw ()
  | _ => do throw ()

def Fin2Term.toLit (t : Lean.Term) : Lean.PrettyPrinter.UnexpandM Lean.NumLit := do
  return (Lean.Syntax.mkNumLit s!"{←Fin2Term.toNat t}")

macro_rules
  | `([tl $_t $_ids*| $v:num ]) => do`(Stx.bvar $(←Lean.NumLit.toFin2 v))
  | `([tl $_t | $v:ident ]) => `($v)
  | `([tl $_t | !($t) ]) => `($t)
  | `([tl $t $h $ids*| $v:ident ]) => do
    if h.getId = v.getId then `(Stx.bvar $(←Lean.NumLit.toFin2 t))
    else `([tl $(t + 1) $ids* | $v:ident])
  | `([tl $t $ids*| ($v) ]) => `(([tl $t $ids* |$v]))
  | `([tl $t $ids*| λ : $ty. $v]) =>    `(Stx.abs [tyl | $ty] [tl $(t + 1) $ids*|$v])
  | `([tl $t $ids*| λ $i : $ty. $v]) => `(Stx.abs [tyl | $ty] [tl $(t + 1) $i $ids*|$v])
  | `([tl $t $ids*| $a $b]) => `(Stx.app ([tl $t $ids* |$a]) ([tl $t $ids*|$b]))
  | `([tl| $v]) => `([tl 0 | $v])

def Stx.uex_inner : Lean.Syntax.Term → Lean.PrettyPrinter.UnexpandM (Lean.TSyntax `stlc_stx_dbIdx)
  | `($i:ident) => `(stlc_stx_dbIdx|$i:ident)
  | `([tl|$b]) => `(stlc_stx_dbIdx|$b)
  | `($t) =>`(stlc_stx_dbIdx|!($t))

@[app_unexpander Stx.abs]
def Stx.abs.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $t $body) => do `([tl| λ : $(←Ty.uex_inner t) . $(←Stx.uex_inner body)])
  | _ => throw ()

@[app_unexpander Stx.app]
def Stx.app.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $a $b) => do `([tl| ($(←Stx.uex_inner a) $(←Stx.uex_inner b)) ])
  | _ => throw ()

@[app_unexpander Stx.bvar]
def Stx.bvar.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $t) => do `([tl| $(←Fin2Term.toLit t):num ])
  | _ => throw ()

namespace Stx

#check [tl| λ x : 0 → 0 . λ y : 0 .  x y ]

