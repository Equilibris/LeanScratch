import Mathlib.Order.Lattice
import LeanScratch.Domain.ChainTrellis
import LeanScratch.Domain.Continous

namespace Dom

variable {A B C : _} [da : Dom A] [db : Dom B] [dc : Dom C]

instance : Dom (Prod A B) where
  bot_le x := Prod.le_def.mpr ⟨da.bot_le x.fst, db.bot_le x.snd⟩
  complete c hc := ⟨complete (c.map Prod.fst) (hc.map monotone_fst), complete (c.map Prod.snd) (hc.map monotone_snd)⟩
  complete_lub c hc :=
    have hca := complete_lub (c.map Prod.fst) (hc.map monotone_fst)
    have hcb := complete_lub (c.map Prod.snd) (hc.map monotone_snd)
    {
      lub_bound := fun n => Prod.le_def.mpr ⟨hca.lub_bound n, hcb.lub_bound n⟩
      lub_least := fun x h => Prod.le_def.mpr ⟨
        hca.lub_least x.fst (And.left  $ Prod.le_def.mp $ h ·),
        hcb.lub_least x.snd (And.right $ Prod.le_def.mp $ h ·)⟩
    }


instance {I : Type v} {p : I → Type u} [h : ∀ i, PartialOrder (p i)] : PartialOrder ((i : I) → p i) where
  le a b := ∀ i, a i ≤ b i
  le_refl x i := (h i).le_refl (x i)
  le_trans a b c hab hbc i := (hab i).trans (hbc i)
  le_antisymm a b hab hba := funext fun i => (hab i).antisymm (hba i)

instance {I : Type v} {p : I → Type u} [h : ∀ i, Dom (p i)] : Dom ((i : I) → p i) where
  bot := fun i => (h i).bot
  bot_le v i := (h i).bot_le (v i)
  complete c hc i := (h i).complete (c · i) ⟨(hc.chain · i)⟩
  complete_lub c hc := {
    lub_bound := fun _ i =>
      ((h i).complete_lub (c · i) ⟨(hc.chain · i)⟩).lub_bound _
    lub_least := fun v hv i =>
      ((h i).complete_lub (c · i) ⟨(hc.chain · i)⟩).lub_least (v i) (hv · i)
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

def Continous.sep_args {f : A × B → C}
    (mono : Monotone f)
    (hl : ∀ dn hdn e ,
      f ⟨(complete dn hdn), e⟩ =
      complete (dn.map (f ⟨·, e⟩)) (hdn.map $ (two_arg_mono.mpr mono).left e))
    (hr : ∀ d en hen,
      f ⟨d, complete en hen⟩ =
      complete (en.map (f ⟨d, ·⟩)) (hen.map $ (two_arg_mono.mpr mono).right d))
    : Continous f where
  mono := mono
  preserves_lubs c hc:= by
    dsimp [complete]
    generalize_proofs p₁ p₂ p₃
    apply Eq.trans $ hl _ _ _
    change complete (f ⟨Prod.fst $ c ·, complete (c.map Prod.snd) p₂⟩) _ = _
    conv =>
      args
      · args
        intro x
        rw [hr _ _ p₂]
      · skip
    let ct : CT C := fun n m => f ⟨(c n).1, (c m).2⟩
    have hct : ChainTrellis ct := {
      chain := fun n m n' m' hl hr =>
        mono $ Prod.le_def.mpr ⟨
          (Prod.le_def.mp $ hc.le_lift hl).left,
          (Prod.le_def.mp $ hc.le_lift hr).right,
        ⟩
    }
    exact hct.complete_merge

instance Continous.fst : Continous (Prod.fst : A × B → A) :=
  Continous.sep_args
    monotone_fst
    (fun _ _ _ => rfl)
    (fun _ _ _ => complete_const.symm)

instance Continous.snd : Continous (Prod.snd : A × B → B) :=
  Continous.sep_args
    monotone_snd
    (fun _ _ _ => complete_const.symm)
    (fun _ _ _ => rfl)

def _root_.Prod.corec (f₁ : D → D₁) (f₂ : D → D₂) (x : D) : D₁ × D₂ :=
  (f₁ x, f₂ x)

instance [h₁ : Continous f₁] [h₂ : Continous f₂] : Continous (Prod.corec f₁ f₂ : A → B × C) where
  mono :=  fun _ _ h => Prod.le_def.mpr ⟨ h₁.mono h, h₂.mono h, ⟩
  preserves_lubs c hc := Prod.mk.inj_iff.mpr ⟨h₁.preserves_lubs _ _, h₂.preserves_lubs _ _⟩

