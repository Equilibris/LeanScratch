import Mathlib.Order.Lattice
import LeanScratch.Domain.ChainTrellis
import LeanScratch.Domain.Continous
import LeanScratch.Domain.ProdDom
import LeanScratch.Domain.FixedPoint
import LeanScratch.Vec

namespace Dom

variable {A B C : _} [da : Dom A] [db : Dom B] [dc : Dom C]

structure CFunc (A B : Type _) [Dom A] [Dom B] where
  f : A → B
  continous : Continous f

namespace CFunc

instance {x : CFunc A B} : Continous x.f := x.continous

instance : CoeFun (CFunc A B) (fun _ => A → B) := ⟨CFunc.f⟩

instance : PartialOrder (CFunc A B) where
  le a b := ∀ d, a d ≤ b d
  le_refl x v := le_refl _
  le_trans a b c hab hbc v := (hab v).trans (hbc v)
  le_antisymm
    | ⟨a, ca⟩, ⟨b, cb⟩, hab, hba => by
      obtain rfl := funext fun v => (hab v).antisymm (hba v)
      rfl

instance : Dom (CFunc A B) where
  bot := ⟨fun _ => ⊥, ⟨monotone_const, fun c _ => complete_const.symm⟩⟩
  bot_le _ _ := bot_le
  complete c hc := ⟨
    fun v => complete (c · v) ⟨(hc.chain · v)⟩,
    ⟨
      fun a b h => complete_mono fun n => (c n).continous.mono h,
      fun an han => by
        conv =>
          lhs
          args
          intro x
          rw [(c x).continous.preserves_lubs an han]
        /- let ct : CT B := fun x y => (c x).f (an y) -/
        /- change complete (λ x ↦ complete (λ y ↦ ct x y) _) _ -/
        /-      = complete (λ y ↦ complete (λ x ↦ ct x y) _) _ -/
        exact CT.complete_comm _ _
    ⟩
  ⟩
  complete_lub c hc := {
    lub_bound := fun n v =>
      complete_bound n (hc := ⟨(hc.chain · v)⟩)
    lub_least := fun c' hle v =>
      complete_least (c'.f v) fun n => hle n v
  }

def fix (f : CFunc A A) : A := complete (Nat.repeat f · ⊥) ⟨p⟩
  where p | 0   => bot_le | n+1 => f.continous.mono (p n)

instance fix_is_lpfp {f : CFunc A A} : LeastPreFixedPoint f.fix f.f where
  fix := by
    let gen := (Nat.repeat f.f · ⊥)
    dsimp [CFunc.fix]
    change f.f (complete gen _) ≤ complete gen _
    generalize_proofs p₁
    rw [f.continous.preserves_lubs gen p₁]
    apply complete_least
    intro n
    change gen n.succ ≤ _
    exact complete_bound n.succ
  least := fun {d} pfp =>
    complete_least
      d
      (Nat.rec bot_le
        (λ _ ih ↦ le_trans (f.continous.mono ih) pfp.fix))

def fix.mono : Monotone (fix : CFunc A A → A) := fun a b h =>
  complete_mono (Nat.rec bot_le
    (fun n ih =>
      le_trans
        (h (n.repeat a.f ⊥))
        (b.continous.mono ih)))

def fix.chain_fix
    {c : Dom.C (CFunc A A)}
    [hc : Chain c]
    {p₁ : _}
    : ∀ n₁, (c n₁).f (complete (c.map fix) p₁) ≤ (complete (c.map fix) p₁) := by
  intro n₁
  rw [(c n₁).continous.preserves_lubs]
  apply complete_least
  intro n₂
  unfold C.map Function.comp
  have := hc.le_lift $ Nat.le_add_left n₂ n₁
  -- Should be made into a calc block
  apply le_trans ((c n₁).continous.mono $ fix.mono this)
  apply le_trans $ (hc.le_lift $ Nat.le_add_right n₁ n₂) (c (n₁ + n₂)).fix
  apply le_trans fix_is_lpfp.fix
  exact complete_bound (c := fun n => (c n).fix) _

open CFunc in
instance : Continous.Helper (fix : CFunc A A → A) where
  mono := fix.mono
  preserves_lubs c hc := by
    apply complete_least
    intro n
    generalize_proofs p₁
    induction n
    · exact bot_le
    case a.succ n ih =>
      change _ ≤ complete (fix $ c ·) _
      apply complete_least
      intro n₁
      apply le_trans _ $ fix.chain_fix n₁
      apply (c n₁).continous.mono
      exact ih

def curry (f : A × B → C) [hcf : Continous f] : CFunc A (CFunc B C) where
  f a := ⟨(f ⟨a, ·⟩), {
    mono := fun x y h => Continous.mono $ Prod.le_def.mpr ⟨le_refl _, h⟩,
    preserves_lubs := fun c hc => by
      change _ = complete (fun n => f (a, c n)) _
      let mapper := (Prod.corec (Function.const B a) id)
      have mapperCont : Continous mapper := by infer_instance
      have := hcf.preserves_lubs (c.map mapper) (hc.map mapperCont.mono)
      change _ = complete ((c.map mapper).map f) _
      rw [←this]
      change _ = f (complete (Function.const _ a) _, complete c _)
      congr
      exact complete_const.symm
  }⟩
  continous := {
    mono := fun a b h v => hcf.mono $ Prod.le_def.mpr ⟨h, le_refl (a, v).2⟩,
    preserves_lubs := fun c hc => by
      apply (CFunc.mk.injEq _ _ _ _).mpr
      funext a
      let mapper : A → A × B := Prod.corec id (Function.const _ a)
      have mapperCont : Continous mapper := by infer_instance
      have := hcf.preserves_lubs (c.map mapper) (hc.map mapperCont.mono)
      change _ = complete ((c.map mapper).map f) _
      rw [←this]
      change _ = f (complete c _, complete (Function.const _ a) _)
      congr
      exact complete_const.symm,
  }

def mp (f : CFunc A B × A) : B := f.fst f.snd

instance : Continous (CFunc.mp (A := A) (B := B)) where
  mono | ⟨f₁, v₁⟩, ⟨f₂, v₂⟩, h => have := Prod.le_def.mp h
      le_trans (this.left v₁) (f₂.continous.mono this.right)
  preserves_lubs c hc := by
    change (complete (c.map Prod.fst) _).f (complete _ _)
          = complete (fun n ↦ (c n).1.f (c n).2) _
    rw [(complete (c.map Prod.fst) _).continous.preserves_lubs _ _]
    unfold C.map Function.comp
    change complete (fun x => _) _ = complete _ _
    apply le_antisymm
    · apply complete_least _
      intro n
      apply complete_least _
      intro n'
      have le_f : (c n').1.f ≤ (c $ n' + n).1.f := monotone_fst $ hc.le_lift $ Nat.le_add_right n' n
      apply le_trans $ le_f (c n).2
      have le_arg := (c $ n' + n).1.continous.mono $ monotone_snd $ hc.le_lift $ Nat.le_add_left n n'
      apply le_trans le_arg
      let f := (fun n ↦ (c n).1.f (c n).2)
      change f _  ≤ complete f _
      exact complete_bound (n' + n)
    · apply complete_least _
      intro n
      generalize_proofs p₁ p₂
      have : (c n).1.f ≤ (complete (fun x ↦ (c x).1) p₁).f := complete_bound (c := λ n ↦ (c n).1) n
      apply le_trans $ this _
      exact complete_bound (c := fun n => (complete (fun x ↦ (c x).1) p₁) (c n).2) n

