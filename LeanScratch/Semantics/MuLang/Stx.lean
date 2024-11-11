import Mathlib.Data.Nat.PSub
import Mathlib.Data.Rel
import Mathlib.Data.Vector.Basic

-- Inductive and broken datatypes,
-- a type like μ 0 is not valid
inductive MuTy : ℕ → Type
  | unit : MuTy n
  | bvar (idx : Fin n)  : MuTy n
  | sum  (a b : MuTy n) : MuTy n
  | prod (a b : MuTy n) : MuTy n

  | μ (body : MuTy n.succ) : MuTy n

mutual
inductive MuTy.Valid : MuTy n → Prop
  | unit : Valid .unit
  | bvar : Valid (.bvar idx)
  | prod : Valid a → Valid b → Valid (.prod a b)
  | sum  : Valid a → Valid b → Valid (.sum  a b)

  | μ : Ind body → Valid (.μ body)

inductive MuTy.Ind : MuTy (Nat.succ n) → Prop
  | unit : Ind .unit
  | bvarS {idx : Fin (Nat.succ n)} : idx ≠ 0 → Ind (.bvar idx)
  | sum  : Valid a → Valid b → Ind (.sum a b)

  | prod : Ind a → Ind b → Ind (.prod a b)
end

-- Expresses types that have non-first class functions
inductive Ty
  | direct (body : MuTy 0) (h : body.Valid)
  | arr    (arg  : MuTy 0) (h :  arg.Valid) (ret : Ty)

example : ¬(MuTy.Valid (@MuTy.μ 0 (.bvar 0))) := fun
  | .μ (.bvarS h) => h rfl

abbrev NatTy : MuTy 0 := .μ (.sum .unit (.bvar 0))

example : NatTy.Valid := .μ (.sum .unit .bvar)

-- I either need a way of equating types or ensuring they are equal of some other form

