
inductive T (P : Type _)
  | prim (p : P)
  | fsl (a b : T P) -- /
  | bsl (a b : T P) -- \

structure RCatGrammar (S : Type) where
  Pr : Type
  s : Pr
  r : S → T Pr

inductive S  where | a | b | c | d | e
inductive Pr where | S | X

inductive Derive (r : S → T P) : T P → List S → Prop
  | prim (v : S) : Derive r (r v) [v]
  | fsl : Derive r (.fsl A B) s₁ → Derive r B s₂ → Derive r A (s₁ ++ s₂)
  | bsl : Derive r B s₁ → Derive r (.bsl A B) s₂ → Derive r A (s₁ ++ s₂)

def RCatGrammar.acc (g : RCatGrammar S) : List S → Prop :=
  Derive g.r (.prim g.s)

def G : RCatGrammar S where
  Pr := Pr
  s  := .S
  r | .a => .prim .X
    | .b => .prim .X
    | .c => .bsl (.bsl (.prim .S) (.prim .X)) (.prim .X)
    | .d => .bsl (.bsl (.prim .S) (.prim .X)) (.prim .X)
    | .e => sorry

open Derive
example : G.acc [.a, .b, .c] := (prim .a).bsl $ (prim .b).bsl (prim .c)
example : G.acc [.a, .b, .c, .d] := .fsl sorry $ (prim .a).bsl $ (prim .b).bsl $ prim .c

