import Mathlib.Init.Set
import LeanScratch.LogicProof.PropLogic.Formula

inductive Gentzen : (Set $ Formula Atom) → Formula Atom → Prop
  | t : Gentzen _ .t

  | holds : a ∈ ctx → Gentzen ctx a

  | conjIntro  : Gentzen ctx a →
                 Gentzen ctx b
      → Gentzen ctx (.conj a b)
  | disjlIntro : Gentzen ctx a
      → Gentzen ctx (.disj a b)
  | disjrIntro : Gentzen ctx b
      → Gentzen ctx (.disj a b)
  | impIntro   : Gentzen (ctx ∪ {a}) b
      → Gentzen ctx (.imp a b)
  | iffIntro   : Gentzen (ctx ∪ {a}) b →
                 Gentzen (ctx ∪ {b}) a
      → Gentzen ctx (.iff a b)
  | negIntro : Gentzen (ctx ∪ {a}) .f
      → Gentzen ct (.neg a)

  | conjElim : Gentzen (ctx ∪ {a, b}) v
      → .conj a b ∈ ctx → Gentzen ctx v

  | disjElim : Gentzen (ctx ∪ {a}) v →
               Gentzen (ctx ∪ {b}) v
      → .disj a b ∈ ctx → Gentzen ctx v
