import LeanScratch.Domain.Dom

namespace Dom

variable [dd : Dom D] [de : Dom E] (f : D → E)

class Continous where
  mono : Monotone f
  preserves_lubs (c : C D) (hc : Chain c) :
    f (dd.chain_complete c hc).fst = (de.chain_complete (c.map f) (hc.map mono)).fst

def Continous.helper
    (c : C D) (hc : Chain c)
    (mono : Monotone f)
    (h : f (dd.chain_complete c hc).fst ≤ (de.chain_complete (c.map f) (hc.map mono)).fst)
    :    f (dd.chain_complete c hc).fst = (de.chain_complete (c.map f) (hc.map mono)).fst
    :=
  le_antisymm h $
    (chain_complete (c.map f) _).snd.lub_least
      (f (chain_complete c _).fst)
      (mono $ (chain_complete c _).snd.lub_bound ·)

class Continous.Helper where
  mono : Monotone f
  preserves_lubs (c : C D) (hc : Chain c) :
    f (dd.chain_complete c hc).fst ≤ (de.chain_complete (c.map f) (hc.map mono)).fst

instance [x : Continous.Helper f] : Continous f where
  mono := x.mono
  preserves_lubs c hc :=
    Continous.helper f c hc
      Continous.Helper.mono
      (x.preserves_lubs _ _)


class StrictContinous (f : D → E) extends Continous f where
  bot_to_bot : f dd.bot = de.bot

