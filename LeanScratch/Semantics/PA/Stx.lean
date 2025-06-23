import LeanScratch.Fin2

inductive Lvl
  | tLvl
  | cLvlZ
  | cLvlS (x : Lvl)
  | cAdd  (a b : Lvl)
  | cMax  (a b : Lvl)

inductive Stx : Nat → Type
  | bvar : Fin2 n → Stx n

  | hole : Stx n

  | tT (lvl : Lvl) : Stx n

  | t0 (univ : Lvl) : Stx n
  | e0 (body elim : Stx n) : Stx n

  | t1 (univ : Lvl) : Stx n
  | c1 (univ : Lvl) : Stx n
  | e1 (body elim proof : Stx n) : Stx n

  | t2  (univ : Lvl) : Stx n
  | c2l (univ : Lvl) : Stx n
  | c2r (univ : Lvl) : Stx n
  | e2 (body elim l r : Stx n) : Stx n

  | tNat  (univ : Lvl) : Stx n
  | cNatZ (univ : Lvl) : Stx n
  | cNatS (univ : Lvl) (v : Stx n) : Stx n
  | eNat  (body elim z s : Stx n) : Stx n

  | tFn (l r : Stx n) : Stx n
  | cFn (ty : Stx n) (body : Stx n.succ) : Stx n
  | eFn (fn arg : Stx n) : Stx n

  | tSigma (index : Stx n) (family : Stx n.succ) : Stx n
  | cSigma (l r : Stx n) : Stx n
  | eSigma (body elim f : Stx n) : Stx n

  | tPi (l r : Stx n) : Stx n
  | cPi (tyFn : Stx n) (body : Stx n.succ) : Stx n
  | ePi (fn arg : Stx n) : Stx n



