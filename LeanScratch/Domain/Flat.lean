import Mathlib.Order.Lattice
import LeanScratch.Domain.ChainTrellis
import LeanScratch.Domain.Dom
import LeanScratch.Domain.PartialFunc
import LeanScratch.Domain.Continous
import LeanScratch.Domain.Finite

namespace Dom

inductive Flat (α : Type _) | bot | obj (v : α)
deriving DecidableEq

inductive Flat.Le : Flat α → Flat α → Prop
  | bot_bot : Le .bot .bot
  | bot_obj : Le .bot $ .obj _
  | obj_obj : Le (.obj a) (.obj a)

inductive Flat.Lt : Flat α → Flat α → Prop
  | bot_obj : Lt .bot $ .obj _

instance : LE (Flat α) := ⟨Flat.Le⟩
instance : LT (Flat α) := ⟨Flat.Lt⟩
instance : PartialOrder (Flat α) where
  lt_iff_le_not_le _ _ := ⟨
    fun | .bot_obj => ⟨.bot_obj, fun h => by cases h⟩,
    fun
      | ⟨.bot_obj, _⟩ => .bot_obj
      | ⟨.bot_bot, h⟩ | ⟨.obj_obj, h⟩ => False.elim $ h (by solve_by_elim)
  ⟩
  le_refl | .bot => .bot_bot | .obj _ => .obj_obj
  le_trans
    | .bot, .bot, .bot, .bot_bot, .bot_bot => .bot_bot
    | .obj _, .obj _, .obj _, .obj_obj, .obj_obj => .obj_obj

    | .bot, .obj _, .obj _, .bot_obj, .obj_obj
    | .bot, .bot, .obj _, .bot_bot, .bot_obj => .bot_obj
  le_antisymm : ∀ (a b : Flat α), a ≤ b → b ≤ a → a = b
    | .bot, .bot, .bot_bot, .bot_bot => rfl
    | .obj _, .obj _, .obj_obj, .obj_obj => rfl

def Flat.finite (c : C $ Flat α) (hc : Chain c) : ∃ _ : c.Finite', True := by
  cases h : c 0
  case obj v =>
    refine ⟨⟨[.obj v], .cons (fun _ x => by cases x) .nil, fun n => ?_, fun  x mem => ?_⟩, .intro⟩
    · apply List.mem_singleton.mpr
      induction n
      · exact h
      case succ n ih =>
        exact match h : c n, c n.succ, hc.chain n with
          | .obj _, .obj _, .obj_obj => h.symm.trans ih
          | .bot, _, _ => Flat.noConfusion $ h.symm.trans ih
    · obtain rfl := List.mem_singleton.mp mem
      exact ⟨0, h⟩
  by_cases x : ∃ n w, c n = .obj w
  · rcases x with ⟨nw, w,p⟩
    refine ⟨⟨[.bot, .obj w], .cons ?_ $ .cons (fun _ x => by cases x) .nil, fun n => ?_, fun  x mem => ?_⟩, .intro⟩
    all_goals simp only [List.mem_cons, forall_eq, List.mem_singleton, List.mem_nil_iff, or_false] at *
    · exact Flat.Lt.bot_obj
    · induction n
      · exact .inl h
      next n ih =>
        rcases ih with ih|ih
        · refine match h : c n, h' : c n.succ, hc.chain n with
            | .obj _, .obj _, .obj_obj => Flat.noConfusion $ ih.symm.trans h
            | .bot, .obj _, .bot_obj => ?_
            | .bot, .bot, .bot_bot => .inl rfl
          simp_all only [Nat.succ_eq_add_one, obj.injEq, false_or]
          have := hc.rel (n+1) nw
          rw [h', p] at this
          exact match this with | .inl .obj_obj | .inr .obj_obj => rfl
        · have := hc.chain n
          generalize c n.succ = n1, c n = n2 at this ih
          cases this <;> simp_all
    · rcases mem with rfl|rfl
      exact ⟨0, h⟩; exact ⟨nw, p⟩
  · simp only [not_exists] at x
    have : ∀ n, c n = .bot := fun n =>
      match h : c n with
      | .obj v => False.elim $ x n v h
      | .bot => rfl
    refine ⟨⟨[.bot], .cons (fun _ x => by cases x) .nil, ?_, ?_⟩, .intro⟩
    <;> simp_all

instance : OrderBot (Flat A) where
  bot := .bot
  bot_le | .bot => .bot_bot | .obj _ => .bot_obj

noncomputable instance : FiniteDom (Flat α) where
  chain_fin c hc := .ofFinite' $ Classical.choose $ Flat.finite c hc

def Flat.domainLift (f : PFun A B) : Flat A → Flat B
  | .bot => .bot
  | .obj x => if let .some x := f x then .obj x else .bot

def Flat.domainLift.mono : Monotone (domainLift f)
  | .obj _, .obj _, .obj_obj => by
    dsimp [Flat.domainLift]
    split
    exact .obj_obj
    exact .bot_bot
  | .bot,   .obj _,  .bot_obj => by
    dsimp [Flat.domainLift]
    split
    exact .bot_obj
    exact .bot_bot
  | .bot,   .bot,    .bot_bot => .bot_bot

variable [DecidableEq B]

noncomputable instance  : Continous (Flat.domainLift f : Flat A → Flat B) :=
  Continous.finite Flat.domainLift.mono

noncomputable instance : StrictContinous (Flat.domainLift f : Flat A → Flat B) := ⟨rfl⟩
