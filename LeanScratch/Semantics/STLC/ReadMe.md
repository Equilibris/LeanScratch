# Proof of strong-normalization of STLC

This directory includes a (quite longwinded) proof of SN(STLC). There are a bunch of lemmas that are required to prove this statement and corollary that are included in this directory. Here is the general structure of these proofs:

- (SN) StrongNorm.lean
  - Contains the actual proof of strong normalization
  - (AC) ArgCount.lean
    - Contains the definition for the construct we denote types into
  - (CT) CTySpec.lean
    - Identical to (TY) but defined in `Type` for recursive motive reasons
    - Subsingleton and equivalance with `TySpec` is provided
  - (TA) TyArr.lean
    - Dependent `ArgCount` mapping for `List Ty`
  - (UB) upperBoundRed.lean
    - The upper bound construction for STLC
- (IF) Infer.lean
  - A simple type-inference algorithm for STLC
  - Proof of correctness for `infer`
- (RD) Red.lean
  - Definition of `Red` relation for STLC
  - Trans and TransRefl closures of Red
  - (BL) Beta.lean
  - (BC) BetaCorrect.lean
  - (RS) RefSet.lean
  - (TM) Terminal.lean
  - (VF) VarFwd.lean
- (ST) Step.lean
- (SX) Stx.lean
  - Defines expression syntax `Stx`
  - Defines type syntax `Ty`
- (TY) Typed.lean
  - Defines typing relation `TySpec`

```mermaid
flowchart TD

AC & CT & TA & UB --> SN
TY --> AC
AC & TA & CT --> UB
AC & CT -> TA


```
