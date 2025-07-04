import LeanScratch.Domain.FuncDom
import Mathlib.Order.Hom.Basic

namespace Dom

class Ccss (α : Type u) [da : Dom α] {β : _} [m : Dom β] (f : CFunc β β) where
  toFun : α → β
  inj : Function.Injective toFun
  embed : toFun a ≤ toFun b ↔ a ≤ b 
  stable i : ∃ o, f (toFun i) = toFun o

namespace Ccss

variable [da : Dom α] [db : Dom β] {f : CFunc β β} (cs : Ccss α f)

def toOrderEmbedding : OrderEmbedding α β where
  toFun := cs.toFun
  inj' := cs.inj
  map_rel_iff' := cs.embed

instance toFun_continous : Continous.Helper cs.toFun where
  mono _ _ h := embed.mpr h
  preserves_lubs c hc := by
    generalize_proofs p
    have club := complete_lub c hc
    have c'lub := complete_lub _ p
    generalize complete c hc = x, complete _ p = y at club c'lub
    have : Lub (c.map (toFun f)) (toFun f x) := {
      lub_least := fun v h => by
        by_cases h' : ∃ x, cs.toFun x ≤ v
        · rcases h' with ⟨w, h'⟩
          apply le_trans _ h'
          apply cs.embed.mpr
          apply club.lub_least w
          intro n
          specialize h n
          sorry
          /- apply cs.embed.mp h -/
        · change ∀ n, cs.toFun (c n) ≤ _ at h
          sorry
      lub_bound := fun n => 
        cs.embed.mpr (Lub.lub_bound n)
    }
    sorry

noncomputable def trace : CFunc α α where
  f := fun inp => Classical.choose $ cs.stable inp
  continous := {
    mono := fun a b h => by
      generalize_proofs p₁ p₂
      have h₁ := Classical.choose_spec p₁
      have h₂ := Classical.choose_spec p₂
      generalize Classical.choose p₁ = x, Classical.choose p₂ = y at h₁ h₂
      have : f.f (toFun f a) ≤ f.f (toFun f b) := f.continous.mono $ embed.mpr h
      rw [h₁, h₂] at this
      exact embed.mp this
    preserves_lubs := fun c hc => by
      generalize_proofs p₁ p₂ p₃
      /- let xc : C β := (toFun f $ c ·) -/
      /- have hxc : Chain xc := sorry -/
      /- have := f.continous.preserves_lubs xc hxc -/
      /- have := fun inp => Classical.choose_spec $ p₂ inp -/
      apply cs.inj
      rw [←Classical.choose_spec p₁]
      sorry
  }

theorem fix_mem : ∃ o, f.fix = cs.toFun o := by
  dsimp [CFunc.fix]
  sorry

