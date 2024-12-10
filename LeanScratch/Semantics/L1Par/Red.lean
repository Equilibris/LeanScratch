import LeanScratch.Semantics.Conc.Stx
import Batteries.Data.HashMap.Basic
import Mathlib.Data.Rel
import Mathlib.Data.List.AList
import LeanScratch.Relation

namespace L1Par

abbrev VarMap := AList (fun _ : String => Int)
abbrev MtxMap := AList (fun _ : String => Bool)

inductive Act
  | tau
  | ass (addr : String) (v : Int)
  | drf (addr : String) (v : Int)
  | lock (addr : String)
  | unlock (addr : String)

inductive TLRed : TExpr → TExpr → Act → Prop
  | op_add : TLRed (.op (.int a) .add (.int b)) (.int (a + b)) .tau
  | op_gte : TLRed (.op (.int a) .gte (.int b)) (.bool (a >= b)) .tau

  | op1 : TLRed a a' act
      → TLRed (.op a op b) (.op a' op b) act
  | op2 : b.IsValue → TLRed a a' act
      → TLRed (.op b op a) (.op b op a') act

  | deref : TLRed (.deref l) (.int v) (.drf l v)
  | ass1  : TLRed (.assign l (.int v)) .skip (.ass l v)
  | ass2  : TLRed a a' act
      → TLRed (.assign l a) (.assign l a') act

  | seq1  : TLRed (.seq .skip a) a .tau
  | seq2  : TLRed a a' act → TLRed (.seq a b) (.seq a' b) act

  | if_t : TLRed (.eif (.bool .true) a b)  a .tau
  | if_f : TLRed (.eif (.bool .false) a b) b .tau
  | if_cond : TLRed a a' act
      → TLRed (.eif a t f) (.eif a' t f) act

  | ewhile : TLRed (.ewhile c body) (.eif c (.seq body $ .ewhile c body) .skip) .tau

  | lock   : TLRed (.lock   s) .skip (.lock   s)
  | unlock : TLRed (.unlock s) .skip (.unlock s)

inductive GRed : Expr → VarMap → MtxMap → Expr → VarMap → MtxMap → Prop
  | tau    : TLRed e e' .tau
      → GRed (.tex e) store mtx (.tex e') store mtx
  | drf    : TLRed e e' (.drf addr n) → store.lookup addr = .some n
      → GRed (.tex e) store mtx (.tex e') store mtx
  | ass    : TLRed e e' (.ass addr n)
      → GRed (.tex e) store mtx (.tex e') (store.insert addr n) mtx
  | lock   : TLRed e e' (.lock addr) → mtx.lookup addr = .some .false
      → GRed (.tex e) store mtx (.tex e') store (mtx.insert addr .true)
  | unlock : TLRed e e' (.unlock addr)
      → GRed (.tex e) store mtx (.tex e') store (mtx.insert addr .false)

  | par1 : GRed a ctx mtx a' ctx' mtx'
      → GRed (.par a b) ctx mtx (.par a' b) ctx' mtx'
  | par2 : GRed a ctx mtx a' ctx' mtx'
      → GRed (.par b a) ctx mtx (.par b a') ctx' mtx'

def Expr.paralize : Expr → List TExpr
  | .par a b => a.paralize ++ b.paralize
  | .tex v   => [v]

inductive TParRed : List TExpr → VarMap → MtxMap → List TExpr → VarMap → MtxMap → Prop
  | tau    : TLRed e e' .tau
      → TParRed (e :: tl) store mtx (e' :: tl) store mtx
  | drf    : TLRed e e' (.drf addr n) → store.lookup addr = .some n
      → TParRed (e :: tl) store mtx (e' :: tl) store mtx
  | ass    : TLRed e e' (.ass addr n)
      → TParRed (e :: tl) store mtx (e' :: tl) (store.insert addr n) mtx
  | lock   : TLRed e e' (.lock addr) → mtx.lookup addr = .some .false
      → TParRed (e :: tl) store mtx (e' :: tl) store (mtx.insert addr .true)
  | unlock : TLRed e e' (.unlock addr)
      → TParRed (e :: tl) store mtx (e' :: tl) store (mtx.insert addr .false)

  | par    : TParRed tl ctx mtx tl' ctx' mtx'
      → TParRed (e :: tl) ctx mtx (e :: tl') ctx' mtx'



