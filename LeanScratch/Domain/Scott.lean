import LeanScratch.Domain.FuncDom
import Mathlib.Order.Hom.Basic
import Mathlib.Data.Set.Basic

namespace Dom

class Ccss
    (α : Type u) {β : outParam (Type _)}
    [m : Dom β] (f : outParam (CFunc β β))
    extends Dom α where
  toFun : α → β
  inj : Function.Injective toFun
  embed : m.le (toFun a) (toFun b) ↔ le a b

  contains_bot : toFun ⊥ = ⊥
  chain_closed (c : C α) hc : ∃ o, m.complete (c.map toFun) hc = toFun o

  stable i : ∃ o, f (toFun i) = toFun o


namespace Ccss

variable [db : Dom β] {f : CFunc β β} (cs : Ccss α f)

def fromContinous [da : Dom α]
    {f : α → β} (hf : Continous f)
    (c : C α) hc
    : complete (c.map f) (hc.map hf.mono) = f (complete c hc) := by
  rw [hf.preserves_lubs]

def toOrderEmbedding : OrderEmbedding α β where
  toFun := cs.toFun
  inj' := cs.inj
  map_rel_iff' := cs.embed

instance : Continous.Helper cs.toFun where
  mono _ _ h := embed.mpr h
  preserves_lubs c hc := by
    generalize_proofs p
    have ⟨w, h⟩ := cs.chain_closed c p
    have := complete_lub _ p
    rw [h] at this ⊢
    exact embed.mpr $ complete_least w fun n => embed.mp (this.lub_bound n)

noncomputable def trace.mapper (inp : α) : α := Classical.choose $ cs.stable inp

noncomputable def trace : CFunc α α where
  f := trace.mapper cs
  continous := {
    mono := fun a b h => by
      dsimp [trace.mapper]
      generalize_proofs p₁ p₂
      have h₁ := Classical.choose_spec p₁
      have h₂ := Classical.choose_spec p₂
      generalize Classical.choose p₁ = x, Classical.choose p₂ = y at h₁ h₂
      have : f.f (toFun a) ≤ f.f (toFun b) := f.continous.mono $ embed.mpr h
      rw [h₁, h₂] at this
      exact embed.mp this
    preserves_lubs := fun c hc => by
      dsimp [trace.mapper]
      generalize_proofs p₁ p₃
      apply cs.inj
      rw [←Classical.choose_spec p₁]
      have i : Continous cs.toFun := by infer_instance
      rw [i.preserves_lubs, i.preserves_lubs, f.continous.preserves_lubs]
      congr
      refine funext fun n ↦ Classical.choose_spec $ cs.stable (c n)
  }

theorem fix_mem : f.fix = cs.toFun (trace cs).fix := by
  unfold CFunc.fix
  rw [(show Continous cs.toFun from by infer_instance).preserves_lubs]
  congr
  funext n
  induction n
  · exact cs.contains_bot.symm
  case succ n ih =>
    change f.f _ = cs.toFun (trace.mapper cs _)
    rw [ih]
    exact Classical.choose_spec (cs.stable _)

structure Admissible (f : CFunc β β) (Φ : β → Prop) : Prop where
  hBot : Φ ⊥
  hStab : ∀ x, Φ x → Φ (f x)
  hLub c hc : (∀ i, Φ (c i)) → Φ (complete c hc)

def monotone_val [Preorder α] {p : α → Prop} : Monotone (Subtype.val (p := p)) := fun _ _ h => h

namespace Admissible

instance toDom
    (h : Admissible f Φ)
    : Dom (Subtype Φ) where
  bot := ⟨⊥, h.hBot⟩
  bot_le x := bot_le x.val
  complete c hc :=
    let   c' := c.map Subtype.val
    have hc' := hc.map monotone_val
    ⟨complete c' hc', h.hLub c' hc' (fun n => Subtype.prop (c n))⟩
  complete_lub c hc :=
    have := complete_lub (c.map Subtype.val) (hc.map monotone_val)
    {
      lub_least := fun x => this.lub_least x
      lub_bound := this.lub_bound
    }

def toCcss
    (h : Admissible f Φ)
    : Ccss (Subtype Φ) f where
  __ := h.toDom

  toFun := Subtype.val
  inj := Subtype.val_injective

  embed := Subtype.coe_le_coe
  contains_bot := rfl
  chain_closed c hc := ⟨
    h.toDom.complete c ⟨fun n => hc.chain n⟩,
    Ccss.fromContinous
      ⟨fun _ _ => id, fun _ _ => rfl⟩
      _ _
  ⟩
  stable := fun i => ⟨⟨f.f i.val, h.hStab i.val i.prop⟩, rfl⟩

end Admissible

theorem scott
    {Φ : β → Prop}
    (h : Admissible f Φ)
    : Φ f.fix :=
  (congrArg Φ (fix_mem h.toCcss)).mpr $ Subtype.prop _

instance union (hs : Admissible f S) (ht : Admissible f T)
    : Admissible f (Set.instUnion.union S T) where
  hBot := .inl hs.hBot
  hStab
    | x, .inl a => .inl $ hs.hStab x a
    | x, .inr a => .inr $ ht.hStab x a
  hLub c hc holds := sorry

instance inter {S : I → β → Prop} (h : ∀ x, Admissible f (S x))
    : Admissible f (∀ i, S i ·) where
  hBot i := (h i).hBot
  hStab x hi i := (h i).hStab x (hi i)
  hLub c hc holds i :=
    (h i).hLub
      c hc
      fun n => holds n i



