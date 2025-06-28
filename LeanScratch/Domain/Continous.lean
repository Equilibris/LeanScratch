import LeanScratch.Domain.Dom

namespace Dom

variable [dd : Dom D] [de : Dom E] (f : D → E)

class Continous where
  mono : Monotone f
  preserves_lubs (c : Chain D) :
    f (dd.chain_complete c).lub = (de.chain_complete $ c.map f mono).lub

def Continous.helper
    (c : Chain D)
    (mono : Monotone f)
    (h : f (chain_complete c).lub ≤ (chain_complete (c.map f mono)).lub)
    :    f (chain_complete c).lub = (chain_complete (c.map f mono)).lub :=
  le_antisymm h $
    (chain_complete (c.map f mono)).lub_least
      (f (chain_complete c).lub)
      (mono $ (chain_complete c).lub_bound ·)

class Continous.Helper where
  mono : Monotone f
  preserves_lubs (c : Chain D) :
    f (dd.chain_complete c).lub ≤ (de.chain_complete $ c.map f mono).lub

instance [x : Continous.Helper f] : Continous f where
  mono := x.mono
  preserves_lubs c :=
    Continous.helper f c
      Continous.Helper.mono
      $ x.preserves_lubs _


class StrictContinous (f : D → E) extends Continous f where
  bot_to_bot : f dd.bot = de.bot

