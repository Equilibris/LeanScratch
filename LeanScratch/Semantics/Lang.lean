import LeanScratch.Relation

structure Lang where
  stx : Type u
  sta : Type u

  red : stx × sta → stx × sta → Prop

structure DetLang extends Lang where
  deterministic : Relation.isFn red
