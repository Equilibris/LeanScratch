import Mathlib.Order.Lattice
import LeanScratch.Domain.ChainTrellis
import LeanScratch.Domain.Dom
import LeanScratch.Domain.PartialFunc
import LeanScratch.Domain.Continous

namespace Dom

inductive Flat (α : Type _) | bot | obj (v : α)

inductive Flat.Le : Flat α → Flat α → Prop
  | bot_bot : Le .bot .bot
  | bot_obj : Le .bot $ .obj _
  | obj_obj : Le (.obj a) (.obj a)

instance : LE (Flat α) := ⟨Flat.Le⟩
instance : PartialOrder (Flat α) where
  le_refl | .bot => .bot_bot | .obj _ => .obj_obj
  le_trans
    | .bot, .bot, .bot, .bot_bot, .bot_bot => .bot_bot
    | .obj _, .obj _, .obj _, .obj_obj, .obj_obj => .obj_obj

    | .bot, .obj _, .obj _, .bot_obj, .obj_obj
    | .bot, .bot, .obj _, .bot_bot, .bot_obj => .bot_obj
  le_antisymm : ∀ (a b : Flat α), a ≤ b → b ≤ a → a = b
    | .bot, .bot, .bot_bot, .bot_bot => rfl
    | .obj _, .obj _, .obj_obj, .obj_obj => rfl

def Flat.finite (c : C $ Flat α) (hc : Chain c) : ∃ _ : c.finite, True := by
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
    · exact Flat.Le.bot_obj
    · induction n
      · exact .inl h
      next n ih =>
        rcases ih with ih|ih
        · refine match h : c n, h' : c n.succ, hc.chain n with
            | .obj _, .obj _, .obj_obj => Flat.noConfusion $ ih.symm.trans h
            | .bot, .obj _, .bot_obj => ?_
            | .bot, .bot, .bot_bot => .inl rfl
          simp_all
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

instance : LawfulBot (Flat α) where
  bot := .bot
  bot_le | .bot => .bot_bot | .obj _ => .bot_obj

noncomputable instance : Dom (Flat α) where
  bot_le := instLawfulBotFlat.bot_le
  chain_complete c hc := ⟨_, Lub.finite $ Classical.choose $ Flat.finite c hc⟩

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

noncomputable instance : Continous.Helper (Flat.domainLift f) where
  mono := Flat.domainLift.mono

  preserves_lubs c hc := by
    generalize chain_complete c _ = club, (chain_complete (c.map (Flat.domainLift f)) _) = club'
    cases h : club.fst
    <;> dsimp [Flat.domainLift]
    any_goals split
    any_goals exact bot_le club'.fst
    rename_i v _ x heq
    have ⟨w, .intro⟩ := Flat.finite c hc
    have ⟨n, p⟩ := Lub.finite_mem w club.snd
    apply le_trans _ (club'.snd.lub_bound n)
    simp [Flat.domainLift, C.map, p, h, heq]

noncomputable instance : StrictContinous (Flat.domainLift f) := ⟨rfl⟩
