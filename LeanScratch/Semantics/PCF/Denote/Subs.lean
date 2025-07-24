import LeanScratch.Semantics.PCF.Denote.Defs

open Dom

namespace PCF

variable {C : _} [Dom A] [Dom B] [Dom C]

def comp_eq {z : CFunc B C} {a b : CFunc A B} (h : a x = b y) : z.comp a x = z.comp b y := by
  dsimp [CFunc.comp]
  rw [h]

def extend (s : CFunc (context Γ) (τ.denote × context Γ))
    : {Γ' : _}
    → CFunc (context (Γ' ++ Γ)) (context (Γ' ++ [τ] ++ Γ))
  | [] => s
  | _ :: _ => CFunc.corecP CFunc.fst
    $ (extend s).comp CFunc.snd

open CFunc in
open Expr in
theorem subst_lem {u : Expr Γ τ} {τo : Ty} : {t : Expr (Γ' ++ [τ] ++ Γ) τo} →
      (t.replace u).denote =
      t.denote.comp (extend $ corecP u.denote .id)
  | .tt | .zero | .ff => by unfold replace; rfl
  | .fix x | .z? x | .pred x | .succ x => by
    unfold replace; dsimp [denote]; rw [subst_lem]
  | .app fn arg => by
    unfold replace; dsimp [denote]
    rw [subst_lem]
    sorry
  | .abs ty' body => by
    unfold replace; dsimp [denote]
    rw [subst_lem]
    sorry
  | .bvar idx => sorry
  | .eif _ _ _ => sorry


