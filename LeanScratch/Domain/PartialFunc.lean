/- import Mathlib.Order.Lattice -/
import LeanScratch.Domain.Dom

namespace Dom

def PFun (A B : Type) := A → Option B

infixr:50 "⇀" => PFun

instance : LE (PFun A B) where
  le a b := ∀ z v, a z = .some v → b z = .some v

instance : PartialOrder (PFun A B) where
  le_refl a z _ := id
  le_trans a b c hab hbc z v := hbc z v ∘ hab z v
  le_antisymm a b hab hba := funext fun x => by
    by_cases ha : ∃ v, a x = some v
    · rcases ha with ⟨w, p⟩
      exact p.trans (hab _ w p).symm
    by_cases hb : ∃ v, b x = some v
    · simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at ha
      rcases hb with ⟨w, p⟩
      exact Option.noConfusion $ ha.symm.trans (hba _ _ p)
    · simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at ha hb
      exact ha.trans hb.symm

variable [DecidableEq B]
instance : Inf (PFun A B) where
  inf a b z := match a z, b z with
    | .some a, .some b =>
      if a = b then
        .some a
      else .none
    | .some _, .none | .none, .some _ | .none, .none => .none

instance : SemilatticeInf (PFun A B) where
  inf_le_left  a b z w h := by
    dsimp [Inf.inf] at h
    split at h
    <;> try exact Option.noConfusion h
    split at h
    · rename_i heq
      subst heq
      obtain rfl := Option.some.inj h
      assumption
    · exact h.elim
  inf_le_right a b z w h := by
    dsimp [Inf.inf] at h
    split at h
    <;> try exact Option.noConfusion h
    split at h
    · rename_i heq
      subst heq
      obtain rfl := Option.some.inj h
      assumption
    · exact h.elim
  le_inf a b c hab hac w v h := by
    dsimp [Inf.inf]
    rw [hab _ _ h, hac _ _ h]
    simp only [↓reduceIte]

noncomputable def PFun.lub (c : C $ PFun A B) : PFun A B := fun a =>
  match Classical.dec (∃ n v, c n a = .some v) with
  | .isTrue  h => c (Classical.choose h) a
  | .isFalse _ => .none

instance : LawfulBot (PFun A B) where
  bot _ := .none
  bot_le _ _ _ := Option.noConfusion

noncomputable instance : Dom (PFun A B) where
  bot_le _ _ _ := Option.noConfusion
  chain_complete c hc := ⟨PFun.lub c, {
    -- The names should be longer here but i have not fixed this yet
    lub_bound := fun n dom cod h => by
      dsimp [PFun.lub]
      split
      next _ h' _ =>
        have ⟨w, p⟩ := Classical.choose_spec h'
        have := hc.rel (Classical.choose h') n
        generalize c (Classical.choose h') = x, c n = y at p this h
        rcases this with h'|h'
        · specialize h' _ _ p
          obtain rfl := Option.some_inj.mp $ h.symm.trans h'
          exact p
        · exact h' _ _ h
      next _ h' _ =>
        exact False.elim $ h' ⟨_, _, h⟩
    lub_least := fun x hLe d cod h => by
      dsimp [PFun.lub] at h
      split at h
      next h' _ => exact hLe (Classical.choose h') _ _ h
      next h' _ => exact Option.noConfusion h
  }⟩

