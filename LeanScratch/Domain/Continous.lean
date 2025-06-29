import LeanScratch.Domain.Dom

namespace Dom

variable [dd : Dom D] [de : Dom E] (f : D → E)

class Continous where
  mono : Monotone f
  preserves_lubs (c : C D) (hc : Chain c) :
    f (complete c hc) = complete (c.map f) (hc.map mono)

def Continous.helper
    (c : C D) (hc : Chain c)
    (mono : Monotone f)
    (h : f (complete c hc) ≤ (complete (c.map f) (hc.map mono)))
    :    f (complete c hc) = (complete (c.map f) (hc.map mono))
    :=
  le_antisymm h $
    (complete_lub (c.map f) _).lub_least
      (f (complete c _))
      (mono $ (complete_lub c _).lub_bound ·)

class Continous.Helper where
  mono : Monotone f
  preserves_lubs (c : C D) (hc : Chain c) :
    f (complete c hc) ≤ complete (c.map f) (hc.map mono)

instance [x : Continous.Helper f] : Continous f where
  mono := x.mono
  preserves_lubs c hc :=
    Continous.helper f c hc
      Continous.Helper.mono
      (x.preserves_lubs _ _)


class StrictContinous (f : D → E) extends Continous f where
  bot_to_bot : f dd.bot = de.bot

