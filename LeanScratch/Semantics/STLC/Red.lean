import LeanScratch.Semantics.STLC.Stx
import LeanScratch.Semantics.STLC.Red.Beta
import Mathlib.Data.Rel
import LeanScratch.Relation

namespace STLC

inductive Red : Stx → Stx → Prop
  | appl  : Red a a' → Red (.app a b ) (.app a' b)
  | appr  : Red b b' → Red (.app a b ) (.app a b')
  | congr : Red a a' → Red (.abs ty a) (.abs ty a')
  | beta  : Red (.app (.abs _ body) v) (body.β v)

abbrev RedStar := Relation.ReflTransGen Red
abbrev RedPlus := Relation.TransGen Red

