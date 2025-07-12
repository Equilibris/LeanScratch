import LeanScratch.Semantics.PCF.Stx
import LeanScratch.Semantics.PCF.Red
import LeanScratch.Domain.Basic

open Dom

namespace PCF

noncomputable def Ty.denote : Ty → Sigma Dom
  | .nat => ⟨Flat Nat, by infer_instance⟩
  | .bool => ⟨Flat Bool, by infer_instance⟩
  | .arrow a b =>
    have ⟨a, ha⟩ := a.denote
    have ⟨b, hb⟩ := b.denote
    ⟨CFunc a b, by infer_instance⟩

noncomputable def context : List Ty → Sigma Dom
  | [] => ⟨Unit, by infer_instance⟩
  | hd :: tl =>
    have ⟨dtl, htl⟩ := context tl
    have ⟨dhd, hhd⟩ := hd.denote
    ⟨dhd × dtl, by infer_instance⟩

namespace Expr
def succ.denote' : Flat Nat → Flat Nat
  | .obj v => .obj v.succ
  | .bot => .bot

noncomputable instance succ.denote'.cont : Continous.Helper (succ.denote') where
  mono
    | .obj a, .obj _, .obj_obj => .obj_obj
    | .bot, .obj b, h => .bot_obj
    | .bot, .bot, h => .bot_bot
  preserves_lubs c hc := by
    dsimp [complete]
    have ⟨f, .intro⟩ := Flat.finite c hc
    sorry

def succ.denote : CFunc (Flat Nat) (Flat Nat) where
  f := succ.denote'
  continous := succ.denote'.cont 

def pred.denote : Flat Nat → Flat Nat
  | .obj (.succ v) => .obj v
  | .obj 0 => .bot
  | .bot => .bot

def z?.denote : Flat Nat → Flat Bool
  | .obj (.succ _) => .obj .false
  | .obj 0 => .obj .true
  | .bot => .bot

def bvar.denote : {Γ : _} → (v : Fin2 Γ.length) → (context Γ).fst → (Γ.getFin2 v).denote.fst
  | _ :: _, .fz, ⟨o, _⟩ => o
  | _ :: _, .fs v, ⟨_, t⟩ => bvar.denote v t

#check CFunc.mp

