import Mathlib.Order.Lattice
import LeanScratch.Domain.ChainTrellis
import LeanScratch.Domain.Continous

namespace Dom

variable [da : Dom A] [db : Dom B] [dc : Dom C]

instance : Dom (Prod A B) where
  bot_le x := Prod.le_def.mpr ⟨da.bot_le x.fst, db.bot_le x.snd⟩
  chain_complete c :=
    have ca := chain_complete $ c.map Prod.fst monotone_fst
    have cb := chain_complete $ c.map Prod.snd monotone_snd
    {
      lub := ⟨ca.lub, cb.lub⟩
      lub_bound := fun n => Prod.le_def.mpr ⟨ca.lub_bound n, cb.lub_bound n⟩
      lub_least := fun x h => Prod.le_def.mpr ⟨
        ca.lub_least x.fst (And.left  $ Prod.le_def.mp $ h ·),
        cb.lub_least x.snd (And.right $ Prod.le_def.mp $ h ·)⟩
    }


def two_arg_mono
    {f : A × B → C}
    : (∀ b a a', a ≤ a' → f ⟨a, b⟩ ≤ f ⟨a', b⟩) ∧
      (∀ a b b', b ≤ b' → f ⟨a, b⟩ ≤ f ⟨a, b'⟩)
    ↔ Monotone f := ⟨
    fun h x y lt =>
      have ⟨l, r⟩ := Prod.le_def.mp lt
      le_trans (h.left x.snd x.fst y.fst l) (h.right y.fst x.snd y.snd r),
    fun h => ⟨
      fun _ _ _ hl => h $ Prod.le_def.mpr ⟨hl, le_refl _⟩,
      fun _ _ _ hr => h $ Prod.le_def.mpr ⟨le_refl _, hr⟩,
    ⟩
  ⟩



instance {f : A × B → C}
    (mono : Monotone f)
    (hl : ∀ dn e ,
      f ⟨(chain_complete dn).lub, e⟩ =
      (chain_complete $ dn.map (f ⟨·, e⟩) $ (two_arg_mono.mpr mono).left e).lub)
    (hr : ∀ d en ,
      f ⟨d, (chain_complete en).lub⟩ =
      (chain_complete $ en.map (f ⟨e, ·⟩) $ (two_arg_mono.mpr mono).right e).lub)
    : Continous f where
  mono := mono
  preserves_lubs := fun c => by
    generalize chain_complete (c.map f _) = y
    dsimp [chain_complete]
    generalize chain_complete (c.map Prod.fst _) = xa, chain_complete (c.map Prod.snd _) = xb
    let ct : ChainTrellis C := {
      gen := fun n m => f ⟨Prod.fst $ c.gen n, Prod.snd $ c.gen n⟩,
      chain := fun _ _ _ _ hl hr =>
        mono $ Prod.le_def.mpr ⟨
          monotone_fst $ Chain.le_lift c hl,
          monotone_snd $ Chain.le_lift c hl
        ⟩
    }
    have : ct.diag = c.map f mono := (Chain.mk.injEq _ _ _ _).mpr $ funext fun x ↦ rfl
    have heq : HEq c $ chain_complete ct.diag := by
      apply?
    sorry


