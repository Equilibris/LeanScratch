import LeanScratch.Fin2
import LeanScratch.Vec
import LeanScratch.Vec2

import LeanScratch.Computation.ComputableFuns

namespace Comp

/- whatsnew in -/
inductive GRFunStx (PRec : Type) [Subsingleton PRec] : Nat → Type
  | zero : GRFunStx PRec arity
  | succ : GRFunStx PRec 1
  | proj (sel : Fin2 arity) : GRFunStx PRec arity
  | comp
      (base : GRFunStx PRec iArr)
      -- Cannot be an inductive due to magic type theory nonsense
      --   (kernel) invalid nested inductive datatype 'Vec', nested inductive datatypes parameters cannot contain local variables.
      --   (args : Vec (GRFunStx PRec oArr) iArr)
      (args : Fin2 iArr → GRFunStx PRec oArr)
      : GRFunStx PRec oArr

  | nRec
      (zCase : GRFunStx PRec args)
      -- n %:: motive n %:: args
      (sCase : GRFunStx PRec (args + 2))
      : GRFunStx PRec (args + 1)

  | mini
      -- return the first value for which the output is zero (a break)
      (enable : PRec)
      (selector : GRFunStx PRec (args + 1))
      : GRFunStx PRec args

def GRFunStx.size [Subsingleton PRec] : GRFunStx PRec arity → Nat
  | .zero | .succ | .proj _ => 1
  | .comp base args =>
    (Vec2.toVec fun x => (args x).size + 1).toList.foldl Nat.add (base.size + 1)
  | .nRec a b => a.size + b.size + 1
  | .mini _ sel => sel.size + 1

def GRFunStx.enableMini [Subsingleton EPre] [Subsingleton EPost] [Inhabited EPost] : GRFunStx EPre arity → GRFunStx EPost arity
  | .zero => .zero
  | .succ => .succ
  | .proj sel => .proj sel
  | .comp base args => .comp base.enableMini fun inp => (args inp).enableMini
  | .mini _ sel => .mini default sel.enableMini
  | .nRec z s => .nRec z.enableMini s.enableMini

def GRFunStx.primDenote : GRFunStx Empty n → Vec Nat n → Nat
  | .zero => fun _ => 0
  | .succ => fun %[x] => x.succ
  | .proj sel => (·.lookup sel)
  | .comp base args => fun inp => base.primDenote $ Vec2.toVec fun x => (args x).primDenote inp
  | .nRec zCase sCase =>
    let zCase := zCase.primDenote
    let sCase := sCase.primDenote
    fun | h %:: tl => h.rec (zCase tl) (sCase $ · %:: · %:: tl)

class PrimComputable (f : Vec Nat ina → Vec Nat outa) where
  progs  : Vec (GRFunStx Empty ina) outa
  proofs : ∀ idx args, (f args).lookup idx = (progs.lookup idx).primDenote args

@[irreducible]
def PrimComputable.use
    (f : Vec Nat ina → Vec Nat outa)
    (sel : Fin2 outa)
    [inst : PrimComputable f]
    : GRFunStx Empty ina :=
  inst.progs.lookup sel

@[simp]
def PrimComputable.use_def
    {f : Vec Nat ina → Vec Nat outa}
    {sel : Fin2 outa}
    [inst : PrimComputable f]
    : (use f sel).primDenote = Vec.lookup sel ∘ f := by
  unfold use
  ext args
  rw [←proofs]
  rfl

theorem foldl_size
    {ls : List Nat} : x ≤ ls.foldl Nat.add x := 
  match ls with
  | [] => by rfl
  | hd :: _ => calc
    _ ≤ x + hd := Nat.le_add_right x hd
    _ ≤ _      := foldl_size
theorem foldl_mem_size
    {ls : List Nat} (h : ∃ y ∈ ls, x < y)
    : x < ls.foldl Nat.add base := by
  rcases h with ⟨y, hMem, hLt⟩
  induction hMem generalizing base
  · calc
      x < base + y := Nat.lt_add_left base hLt
      _ ≤ _ := foldl_size
  case tail ih => exact ih

mutual
def GRFunStx.denote.compV {Enable : Type} [Subsingleton Enable]
    (gas : ℕ) (zCase : Option ℕ)
    (sCase : GRFunStx Enable (ac + 2)) (args : Vec ℕ ac) : ℕ → Option ℕ
  | 0 => zCase
  | n+1 => do
    let ih ← denote.compV gas zCase sCase args n
    sCase.denote (n %:: ih %:: args) gas
termination_by x => (sCase.size, x)
decreasing_by
all_goals simp_wf
all_goals apply Prod.Lex.right
all_goals omega

def GRFunStx.denote.mini {Enable : Type} [Subsingleton Enable] (cv gas : ℕ)
    (args : Vec Nat ac) (f : GRFunStx Enable (ac + 1)) : Option ℕ :=
  match _h : gas - cv with
  | 0 => .none
  | _ + 1 => do
    let v ← f.denote (cv %:: args) gas
    if v = 0 then some cv
    else denote.mini cv.succ gas args f
termination_by (f.size, gas - cv)
decreasing_by
all_goals simp_wf
all_goals apply Prod.Lex.right
all_goals omega

def GRFunStx.denote [Subsingleton Enable] (f : GRFunStx Enable n) (args : Vec Nat n) (gas : Nat) : Option Nat := match f, args with
  | .zero, _     => .some 0
  | .succ, %[x]  => .some x.succ
  | .proj sel, v => .some $ v.lookup sel
  | .comp (iArr := iArr) base v, args => do
    let args ← Vec.mapM id $ Vec2.toVec fun x => (v x).denote args gas
    base.denote args gas
  | .nRec zCase sCase, hd %:: args => do
    let zCase ← zCase.denote args gas
    denote.compV gas zCase sCase args hd
  | .mini _ f, args => denote.mini 0 gas args f
termination_by (f.size, 0)
decreasing_by
all_goals simp_wf
all_goals apply Prod.Lex.left
all_goals simp only [size]
any_goals omega
· apply foldl_mem_size
  refine ⟨(v x).size + 1, ?_, Nat.lt_add_one (v x).size⟩
  apply Vec.toList_mem
  apply Vec2.Mem_toVec
  exact ⟨x, rfl⟩
· exact foldl_size
  -- Abuse of notation, should use a trans but _ < _ is defined as _ ≤ _.succ
end

theorem GRFunStx.denote_primDenote.args
    {iArr : ℕ} {v : Vec2 Nat iArr}
    : Vec.mapM id (Vec2.toVec $ Option.some ∘ v) = some (Vec2.toVec v) :=
  match iArr with
  | 0 => rfl
  | n+1 => by
    simp only [Vec.mapM, Function.comp_apply, id_eq, Option.map_eq_map,
      Option.bind_eq_bind, Option.some_bind, Vec2.toVec, Option.map_eq_some', Vec.cons.injEq,
      true_and, exists_eq_right]
    exact denote_primDenote.args (iArr := n)

def GRFunStx.denote_primDenote
    [Subsingleton Enable] [Inhabited Enable] {f : GRFunStx Empty n}
    : (f.enableMini (EPost := Enable)).denote args 0 = f.primDenote args :=
  match n, f with
  | _, .proj _ | _, .zero => by
    simp only [enableMini, primDenote, Nat.succ_eq_add_one, denote]
  | _, .succ => by
    rcases args with (_|⟨h, (_|_)⟩)
    simp [denote, enableMini, primDenote]
  | _, .nRec _ _ => by
    rcases args with (_|⟨hd, tl⟩)
    simp only [enableMini, denote, Option.bind_eq_bind]
    rw [denote_primDenote]
    simp only [Option.some_bind]
    induction hd
    <;> simp only [denote.compV, primDenote, Nat.rec_zero, Option.bind_eq_bind]
    case succ ih =>
      rw [ih]
      simp only [denote_primDenote, Option.some_bind, Option.some.injEq]
      rfl
  | _, .comp _ args' => by
    simp only [enableMini, denote, Option.bind_eq_bind, primDenote]
    conv =>
      lhs
      congr
      · congr; case a.a =>
        congr
        ext
        rw [GRFunStx.denote_primDenote]
      · ext
        rw [GRFunStx.denote_primDenote]
    rw [Option.bind_eq_some]
    exact ⟨
      (Vec2.toVec fun x ↦ (args' x).primDenote args),
      denote_primDenote.args,
      rfl
    ⟩

class PRecComputable (f : Vec Nat ina → Vec Nat outa) where
  progs  : Vec (GRFunStx Unit ina) outa
  proofs : ∀ idx args, ∃ gas, .some ((f args).lookup idx) = (progs.lookup idx).denote args gas

namespace CompFuns.GRFs
open PrimComputable in
section

macro "simp_grf" : tactic => `(tactic|
  simp only [
    $(Lean.mkIdent ``PrimComputable.use_def):ident,
    $(Lean.mkIdent ``Vec.lookup):ident,
    $(Lean.mkIdent ``Vec2.toVec):ident,
    $(Lean.mkIdent ``Vec2.cons):ident,
    $(Lean.mkIdent ``Vec2.nil):ident,
    $(Lean.mkIdent ``GRFunStx.primDenote):ident,
    $(Lean.mkIdent ``Function.comp_apply):ident
  ]
)

instance : PrimComputable predf where
  progs := %[.nRec .zero $ .proj .fz]
  proofs | .fz, %[n+1] | .fz, %[0] => by simp_grf; simp

instance : PrimComputable addf where
  progs := %[
    .comp (.nRec (.proj .fz) (.comp .succ (%![.proj $ .fs .fz]))) %![.proj (.fs .fz), .proj .fz]
  ]
  proofs
    | .fz, %[a, b] => by
      simp_grf
      induction b
      · rfl
      case succ ih =>
        dsimp only
        rw [←ih]
        rfl

def constf.prog : Nat → GRFunStx Empty 1
  | 0     => .zero
  | n + 1 => .comp .succ %![prog n]

instance : PrimComputable (constf n) where
  progs := %[constf.prog n]
  proofs
    | .fz, %[x] => by
      simp_grf
      induction n
      · rfl
      case succ ih =>
        simp_grf
        rw [←ih]

instance : PrimComputable subf where
  progs := %[.comp (.nRec (.proj .fz) (.comp (use predf .fz) %![.proj $ .fs .fz])) (%![.proj $ .fs .fz, .proj .fz]) ]
  proofs
    | .fz, %[a, b] => by
      simp_grf
      induction b
      · rfl
      case succ n ih =>
        change (a - n) - 1 = _ - 1
        rw [ih]



end

