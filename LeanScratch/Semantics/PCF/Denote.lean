import LeanScratch.Semantics.PCF.Stx
import LeanScratch.Semantics.PCF.Red
import LeanScratch.Domain.Basic

open Dom

namespace PCF

noncomputable def Ty.denote' : Ty → Sigma Dom
  | .nat => ⟨Flat Nat, by infer_instance⟩
  | .bool => ⟨Flat Bool, by infer_instance⟩
  | .arrow a b =>
    have ⟨a, ha⟩ := a.denote'
    have ⟨b, hb⟩ := b.denote'
    ⟨CFunc a b, by infer_instance⟩

instance {d : Sigma Dom} : Dom d.fst := d.snd

noncomputable def Ty.denote : Ty → Type := Sigma.fst ∘ Ty.denote'
noncomputable instance : Dom (Ty.denote t) := Sigma.snd $ Ty.denote' t

noncomputable def context' : List Ty → Sigma Dom
  | [] => ⟨Unit, by infer_instance⟩
  | hd :: tl =>
    have ⟨dtl, htl⟩ := context' tl
    ⟨hd.denote × dtl, by infer_instance⟩

noncomputable def context : List Ty → Type := Sigma.fst ∘ context'
noncomputable instance : Dom (context t) := Sigma.snd $ context' t

namespace Expr
def succ.denote' : Flat Nat → Flat Nat
  | .obj v => .obj v.succ
  | .bot => .bot
def succ.denote'.mono : Monotone succ.denote' := fun
  | .obj _, .obj _, .obj_obj => .obj_obj
  | .bot,   .obj _, _        => .bot_obj
  | .bot,   .bot,   _        => .bot_bot
instance succ.denote'.cont : Continous succ.denote' :=
  Continous.finite succ.denote'.mono 
def succ.denote : CFunc (Flat Nat) (Flat Nat) where
  f := succ.denote'
  continous := succ.denote'.cont 

def pred.denote' : Flat Nat → Flat Nat
  | .obj (.succ v) => .obj v
  | .obj 0 => .bot
  | .bot => .bot
def pred.denote'.mono : Monotone pred.denote' := fun
  | .obj (_+1), .obj _, .obj_obj => .obj_obj
  | .bot, .obj (.succ _), _ => .bot_obj
  | .bot, .obj 0, _
  | .obj 0, .obj _, .obj_obj
  | .bot, .bot, _ => .bot_bot
instance pred.denote'.cont : Continous pred.denote' :=
  Continous.finite pred.denote'.mono
def pred.denote : CFunc (Flat Nat) (Flat Nat) where
  f := pred.denote'
  continous := pred.denote'.cont 

def z?.denote' : Flat Nat → Flat Bool
  | .obj (.succ _) => .obj .false
  | .obj 0 => .obj .true
  | .bot => .bot
def z?.denote'.mono : Monotone z?.denote' := fun
  | .obj 0, .obj _, .obj_obj | .obj (_+1), .obj _, .obj_obj => .obj_obj
  | .bot, .obj 0, .bot_obj   | .bot,   .obj (_+1), .bot_obj => .bot_obj
  | .bot, .bot, .bot_bot => .bot_bot
instance z?.denote'.cont : Continous z?.denote' :=
  Continous.finite z?.denote'.mono
def z?.denote : CFunc (Flat Nat) (Flat Bool) where
  f := z?.denote'
  continous := z?.denote'.cont

def bvar.denote : {Γ : _} → (v : Fin2 Γ.length) → context Γ → (Γ.getFin2 v).denote
  | _ :: _, .fz, ⟨o, _⟩ => o
  | _ :: _, .fs v, ⟨_, t⟩ => bvar.denote v t

def eif.denote' [Bot τ] : Flat Bool × τ × τ → τ
  | ⟨.obj .true,  v⟩ => Prod.fst v
  | ⟨.obj .false, v⟩ => Prod.snd v
  | ⟨.bot, _, _⟩ => ⊥

def eif.denote'.mono [Preorder τ] [OrderBot τ] : Monotone (eif.denote' : _ → τ) := fun
  | ⟨.bot, _⟩, ⟨.obj .true,  _⟩, ⟨.bot_obj, _⟩
  | ⟨.bot, _⟩, ⟨.obj .false, _⟩, ⟨.bot_obj, _⟩ => bot_le

  | ⟨.obj .true,  _⟩, ⟨.obj .true,  _⟩, ⟨.obj_obj, o, _⟩
  | ⟨.obj .false, _⟩, ⟨.obj .false, _⟩, ⟨.obj_obj, _, o⟩ => o

  | ⟨.bot, _⟩, ⟨.bot, _⟩, ⟨.bot_bot, _⟩ => le_refl _
instance [Dom τ] : Continous (eif.denote' : _ → τ) :=
  Continous.sep_args eif.denote'.mono
    (fun en hen d => by
      have : DecidableEq τ := Classical.typeDecidableEq τ
      rw [FiniteDom.complete_last]
      have m : Monotone (eif.denote' ⟨·, d⟩) :=
        (two_arg_mono.mpr eif.denote'.mono).1 d
      let enFin := FiniteDom.chain_fin en hen
      let map := C.Finite.map (f := (eif.denote' ⟨·, d⟩)) m enFin
      have := C.Finite.complete_last _ (hen.map m) $ map
      rw [this]
      have := C.Finite.ls_map _ m map enFin
      rw [List.getLast_writer this]
      dsimp [List.dedup]
      rw [pw_filter_last, List.getLast_map]
    )
    (fun
      | .bot, en, h => complete_const.symm
      | .obj .true, en, h | .obj .false, en, h => rfl)
def eif.denote [Dom τ] : CFunc (Flat Bool × τ × τ) τ where
  f := eif.denote'
  continous := by infer_instance

def proj
    : {Γ : List Ty}
    → (idx : Fin2 Γ.length)
    → CFunc (context Γ) (Γ.getFin2 idx).denote
  | _ :: _, .fz => CFunc.fst
  | _ :: _, .fs v =>
    CFunc.comp (proj v) CFunc.snd

noncomputable def denote : Expr Γ ret → CFunc (context Γ) ret.denote
  | .fix v => CFunc.comp CFunc.fix' v.denote
  | .app fn arg => CFunc.comp CFunc.mp' (CFunc.corecP fn.denote arg.denote)
  | .abs _ body => CFunc.curry $ CFunc.swap body.denote
  | .bvar idx => proj idx
  | .eif cond t f => CFunc.comp eif.denote (CFunc.corecP cond.denote (CFunc.corecP t.denote f.denote))
  | .z? v => CFunc.comp z?.denote v.denote
  | .pred v => CFunc.comp pred.denote v.denote
  | .succ v => CFunc.comp succ.denote v.denote
  | .zero => CFunc.const $ .obj 0
  | .ff => CFunc.const $ .obj .true
  | .tt => CFunc.const $ .obj .false

