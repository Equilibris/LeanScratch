namespace Athena

inductive Term
  -- de Bruijn index
  | bvar (nat : Nat)

  /- | forceType (val type : Term) -/

  -- Lets you reference a lemma, this is just a reference into a list
  | cut (nat : Nat)

  -- A hole is just an empty place to let the unifier solve for, a hole is not a valid type
  | hole -- (mv : Nat) -- In a perfect world we would allow for MV unification but now we just fail

  -- We allow for type-in-type though it is unsound
  | typeT

  -- Units, node elim is a noop
  | unitT
  | unitIntro
  | unitElim : Term → Term

  -- Sums, these are only needed to bootstrap sigmas to be initialised with non-singleton types.
  -- These are only required to construct types of finite size
  | sumT (a b : Term)
  | inl (bty a : Term)
  | inr (aty b : Term)
  | sumElim (p pForA pForB : Term) -- these proofs might be simpler but i dont know yet

  -- Products are not needed
  /- | prodT (a b : Term) -/
  /- | prodIntro (a b : Term) -/
  /- | fst (bty a : Term) -/
  /- | snd (aty b : Term) -/

  -- Dependent pairs
  | sigmaT (a b : Term)
  | sigmaIntro (fst snd : Term)
  | sigmaElim  (v f : Term) -- For a sigma (x : α) × β x, f : (x : α) → β x → γ

  -- Dependent functions
  | piT (a b : Term)
  | piNdIntro (argT f : Term) -- Aka function types
  | piIntro   (retT f : Term)
  | piElim    (fn arg : Term)

  -- Natural numbers serve to give us AxInf, they let us define inductives in funky ways
  | natT
  | z
  | s (v : Term)
  | natElim (motive v zCase sCase : Term) -- sCase : (n : Nat) → motive n → motive (.s n)

  -- Scary scary equality types. Need to figure out how to work with these...
  | eqT (type a b : Term)
  | eqIntro (type a : Term) -- rfl
  | eqElim (pForA aEqB pForB : Term)

abbrev Term.mp := Term.piElim
abbrev Term.fn := Term.piNdIntro
