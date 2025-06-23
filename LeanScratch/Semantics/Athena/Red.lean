import LeanScratch.Semantics.Athena.Stx

namespace Athena

def Term.bvarShift (shift skip : Nat) : Term → Term
  | .piNdIntro argT f =>
      .piNdIntro (argT.bvarShift shift skip) (f.bvarShift shift skip.succ)
  | .piIntro retT f =>
      .piIntro (retT.bvarShift shift skip) (f.bvarShift shift skip.succ)
  | .piT a b => .piT
      (a.bvarShift shift skip)
      (b.bvarShift shift skip.succ)
  | .sigmaT a b => .sigmaT
      (a.bvarShift shift skip)
      (b.bvarShift shift skip.succ)

  | .bvar n => .bvar $ if n < skip then n else n + shift

  | .unitElim v => .unitElim (v.bvarShift shift skip)
  | .inl bty a => .inl (bty.bvarShift shift skip) (a.bvarShift shift skip)
  | .inr aty b => .inr (aty.bvarShift shift skip) (b.bvarShift shift skip)
  | .sigmaIntro fst snd =>
      .sigmaIntro (fst.bvarShift shift skip) (snd.bvarShift shift skip)
  | .sigmaElim v f =>
      .sigmaElim (v.bvarShift shift skip) (f.bvarShift shift skip)
  | .piElim fn arg =>
      .piElim (fn.bvarShift shift skip) (arg.bvarShift shift skip)
  | .s v => .s (v.bvarShift shift skip)
  | .natElim motive v zCase sCase => .natElim
      (motive.bvarShift shift skip)
      (v.bvarShift shift skip)
      (zCase.bvarShift shift skip)
      (sCase.bvarShift shift skip)
  | .eqElim pForA aEqB pForB => .eqElim
      (pForA.bvarShift shift skip)
      (aEqB.bvarShift shift skip)
      (pForB.bvarShift shift skip)
  | .eqT type a b => .eqT
      (type.bvarShift shift skip)
      (a.bvarShift shift skip)
      (b.bvarShift shift skip)
  | .eqIntro type a => .eqIntro
      (type.bvarShift shift skip)
      (a.bvarShift shift skip)
  | .sumElim p pForA pForB => .sumElim
      (p.bvarShift shift skip)
      (pForA.bvarShift shift skip)
      (pForB.bvarShift shift skip)
  | .sumT a b => .sumT
      (a.bvarShift shift skip)
      (b.bvarShift shift skip)
  | t@z | t@natT | t@unitIntro | t@typeT | t@hole | t@(cut _) | t@unitT => t  -- handles typeT, unitT, unitIntro, z, cut, hole

def Term.replace.bvar (bvarId idx_shift : Nat) (replace : Term) : Term :=
  match compare bvarId idx_shift with
  | .lt => .bvar bvarId
  | .eq => replace.bvarShift idx_shift 0
  | .gt => .bvar (bvarId.pred)

def Term.replace (idx_shift : Nat) (body replace : Term) : Term := match body with
  | .piNdIntro argT f => .piNdIntro
      (argT.replace idx_shift replace)
      (f.replace idx_shift.succ replace)
  | .piIntro retT f => .piIntro
      (retT.replace idx_shift replace)
      (f.replace idx_shift.succ replace)
  | .piT a b => .piT
      (a.replace idx_shift replace)
      (b.replace idx_shift.succ replace)
  | .sigmaT a b => .sigmaT
      (a.replace idx_shift replace)
      (b.replace idx_shift.succ replace)

  | .bvar n => Term.replace.bvar n idx_shift replace

  | .unitElim v => .unitElim (v.replace idx_shift replace)
  | .inl bty a => .inl
      (bty.replace idx_shift replace)
      (a.replace idx_shift replace)
  | .inr aty b => .inr
      (aty.replace idx_shift replace)
      (b.replace idx_shift replace)
  | .sigmaIntro fst snd => .sigmaIntro
      (fst.replace idx_shift replace)
      (snd.replace idx_shift replace)
  | .sigmaElim v f => .sigmaElim
      (v.replace idx_shift replace)
      (f.replace idx_shift replace)
  | .piElim fn arg => .piElim
      (fn.replace idx_shift replace)
      (arg.replace idx_shift replace)
  | .s v => .s (v.replace idx_shift replace)
  | .natElim motive v zCase sCase => .natElim
      (motive.replace idx_shift replace)
      (v.replace idx_shift replace)
      (zCase.replace idx_shift replace)
      (sCase.replace idx_shift replace)
  | .eqElim pForA aEqB pForB => .eqElim
      (pForA.replace idx_shift replace)
      (aEqB.replace idx_shift replace)
      (pForB.replace idx_shift replace)
  | .eqT type a b => .eqT
      (type.replace idx_shift replace)
      (a.replace idx_shift replace)
      (b.replace idx_shift replace)
  | .eqIntro type a => .eqIntro
      (type.replace idx_shift replace)
      (a.replace idx_shift replace)
  | .sumElim p pForA pForB => .sumElim
      (p.replace idx_shift replace)
      (pForA.replace idx_shift replace)
      (pForB.replace idx_shift replace)
  | .sumT a b => .sumT
      (a.replace idx_shift replace)
      (b.replace idx_shift replace)

  | t@z | t@natT | t@unitIntro | t@typeT | t@hole | t@(cut _) | t@unitT => t  -- handles typeT, unitT, unitIntro, z, cut, hole

def β (body repl : Term) : Term := body.replace 0 repl

-- →β : (λ x. body) y = body [y / x]
-- ×β : fst (a, b) = a
-- ×β : snd (a, b) = b

-- →η : λx. f x = f
-- ×η : (fst p, snd p) = p

-- →-congr (f = g) and (a = b) : f a = g b

-- 3 families of types

-- inductives  sums, ~~products~~, Σ, ℕ, Unit, Empty
-- functions   Π, →
-- equiality   Eq

-- Π (_ : α). β ≣ (_ : α) → β ≅ α → β
-- Π : (x : Type) → (x → Type) → Type
-- Π (x : α). β x

-- a + b = b + a

example {a b c : Nat} : a + b + c = a + (b + c) :=
  Nat.rec (motive := fun z => a + b + z = a + (b + z))
    rfl
    (fun x ih =>
      have xAddZ : a + b + x = a + (b + x) := ih
      have p : (a + b + x).succ = (a + (b + x)).succ :=
        (Nat.succ.injEq _ _).mpr xAddZ
      have p : a + b + x.succ = a + (b + x.succ) :=
        p
      p)
    c

example {n : Nat} : 0 + n = n :=
  Nat.rec (motive := fun z => 0 + z = z) rfl (fun x xAddZ =>
    have xAddZ : 0 + x = x := xAddZ
    have p : 0 + (x + 1) = x.succ :=
      Eq.trans (Nat.add_assoc 0 x 1).symm
        $ (Nat.succ.injEq _ _ ).mpr xAddZ
    have p : 0 + x.succ = x.succ :=
      p
    p
    ) n

example {n : Nat} : 0 + n = n := by
  induction n
  · rfl
  case succ ih =>
    rw [←Nat.add_assoc]
    rw [ih]

-- can add η-rules if i can be bothered
inductive Eval (cuts : List Term) : Term → Term → Type
  /- | forceType : Eval _ (.forceType val _) val -/
  | cut (hGet : cuts[c]? = .some v) : Eval cuts (.cut c) v
  | unitβ : Eval cuts (.unitElim v) v
  | sumβa : Eval cuts (.sumElim (.inl _ av) a b) (.mp a av)
  | sumβb : Eval cuts (.sumElim (.inl _ bv) a b) (.mp b bv)
  /- | prodβfst : Eval cuts (.fst _ (.prodIntro a b)) a -/
  /- | prodβsnd : Eval cuts (.snd _ (.prodIntro a b)) b -/
  | sigmaβ : Eval cuts (.sigmaElim (.sigmaIntro fst snd) x) (.mp (.mp x fst) snd)
  | piβnd  : Eval cuts (.mp (.fn      _ a) b) (β a b) -- TODO
  | piβd   : Eval cuts (.mp (.piIntro _ a) b) (β a b) -- TODO
  | natβz  : Eval cuts (.natElim _ .z zCase sCase) zCase
  | natβs  : Eval cuts (.natElim motive (.s n) zCase sCase) ((sCase.mp n).mp (.natElim motive n zCase sCase))

  | unitElimCong :
      Eval cuts v v' →
      Eval cuts (.unitElim v) (.unitElim v')
  | sumElimPCong :
      Eval cuts p p' →
      Eval cuts (.sumElim p pForA pForB) (.sumElim p' pForA pForB)
  | sumElimAForCong :
      Eval cuts pForA pForA' →
      Eval cuts (.sumElim p pForA pForB) (.sumElim p pForA' pForB)
  | sumElimBForCong :
      Eval cuts pForB pForB' →
      Eval cuts (.sumElim p pForA pForB) (.sumElim p pForA pForB')
  | sigmaElimVCong :
      Eval cuts v v' →
      Eval cuts (.sigmaElim v f) (.sigmaElim v' f)
  | sigmaElimFCong :
      Eval cuts f f' →
      Eval cuts (.sigmaElim v f) (.sigmaElim v f')
  | piElimFnCong :
      Eval cuts fn fn' →
      Eval cuts (.piElim fn arg) (.piElim fn' arg)
  | piElimArgCong :
      Eval cuts arg arg' →
      Eval cuts (.piElim fn arg) (.piElim fn arg')
  | natElimMotiveCong :
      Eval cuts motive motive' →
      Eval cuts (.natElim motive v zCase sCase)
               (.natElim motive' v zCase sCase)
  | natElimVCong :
      Eval cuts v v' →
      Eval cuts (.natElim motive v zCase sCase)
               (.natElim motive v' zCase sCase)
  | natElimZCaseCong :
      Eval cuts zCase zCase' →
      Eval cuts (.natElim motive v zCase sCase)
               (.natElim motive v zCase' sCase)
  | natElimSCaseCong :
      Eval cuts sCase sCase' →
      Eval cuts (.natElim motive v zCase sCase)
               (.natElim motive v zCase sCase')
  | eqElimPForACong :
      Eval cuts pForA pForA' →
      Eval cuts (.eqElim pForA aEqB pForB)
               (.eqElim pForA' aEqB pForB)
  | eqElimAEqBCong :
      Eval cuts aEqB aEqB' →
      Eval cuts (.eqElim pForA aEqB pForB)
               (.eqElim pForA aEqB' pForB)
  | eqElimPForBCong :
      Eval cuts pForB pForB' →
      Eval cuts (.eqElim pForA aEqB pForB)
               (.eqElim pForA aEqB pForB')

  -- Congruence rules for introductions
  | inlBtyCong :
      Eval cuts bty bty' →
      Eval cuts (.inl bty a) (.inl bty' a)
  | inlACong :
      Eval cuts a a' →
      Eval cuts (.inl bty a) (.inl bty a')
  | inrAtyCong :
      Eval cuts aty aty' →
      Eval cuts (.inr aty b) (.inr aty' b)
  | inrBCong :
      Eval cuts b b' →
      Eval cuts (.inr aty b) (.inr aty b')
  | sigmaIntroFstCong :
      Eval cuts fst fst' →
      Eval cuts (.sigmaIntro fst snd) (.sigmaIntro fst' snd)
  | sigmaIntroSndCong :
      Eval cuts snd snd' →
      Eval cuts (.sigmaIntro fst snd) (.sigmaIntro fst snd')
  | piNdIntroArgTCong :
      Eval cuts argT argT' →
      Eval cuts (.piNdIntro argT f) (.piNdIntro argT' f)
  | piNdIntroFCong :
      Eval cuts f f' →
      Eval cuts (.piNdIntro argT f) (.piNdIntro argT f')
  | piIntroRetTCong :
      Eval cuts retT retT' →
      Eval cuts (.piIntro retT f) (.piIntro retT' f)
  | piIntroFCong :
      Eval cuts f f' →
      Eval cuts (.piIntro retT f) (.piIntro retT f')
  | sCong :
      Eval cuts v v' →
      Eval cuts (.s v) (.s v')

