import Mathlib.Order.Lattice
import LeanScratch.Domain.ChainTrellis

class Dom.ChainComplete (α : Type _) extends PartialOrder α where
  chain_complete (c : Dom.Chain α) : ∃ _ : Dom.Lub c, True

class Dom (α : Type _) extends Dom.ChainComplete α, Bot α where
  bot_le (x : α) : ⊥ ≤ x

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

instance : Dom (Flat α) where
  bot := .bot
  bot_le | .bot => .bot_bot | .obj _ => .bot_obj

  chain_complete c :=
    have ⟨w, _⟩ : ∃ _ : c.finite, True := by
      cases h : c.gen 0
      case obj v =>
        refine ⟨⟨[.obj v], .cons (fun _ x => by cases x) .nil, fun n => ?_, fun  x mem => ?_⟩, .intro⟩
        · apply List.mem_singleton.mpr
          induction n
          · exact h
          case succ n ih =>
            exact match h : c.gen n, c.gen n.succ, c.chain n with
              | .obj _, .obj _, .obj_obj => h.symm.trans ih
              | .bot, _, _ => Flat.noConfusion $ h.symm.trans ih
        · obtain rfl := List.mem_singleton.mp mem
          exact ⟨0, h⟩
      by_cases x : ∃ n w, c.gen n = .obj w
      · rcases x with ⟨nw, w,p⟩
        refine ⟨⟨[.bot, .obj w], .cons ?_ $ .cons (fun _ x => by cases x) .nil, fun n => ?_, fun  x mem => ?_⟩, .intro⟩
        all_goals simp only [List.mem_cons, forall_eq, List.mem_singleton, List.mem_nil_iff, or_false] at *
        · exact Flat.Le.bot_obj
        · induction n
          · exact .inl h
          next n ih =>
            rcases ih with ih|ih
            · refine match h : c.gen n, h' : c.gen n.succ, c.chain n with
                | .obj _, .obj _, .obj_obj => Flat.noConfusion $ ih.symm.trans h
                | .bot, .obj _, .bot_obj => ?_
                | .bot, .bot, .bot_bot => .inl rfl
              simp_all
              have := c.rel (n+1) nw
              rw [h', p] at this
              exact match this with | .inl .obj_obj | .inr .obj_obj => rfl
            · have := c.chain n
              generalize c.gen n.succ = n1, c.gen n = n2 at this ih
              cases this <;> simp_all
        · rcases mem with rfl|rfl
          exact ⟨0, h⟩; exact ⟨nw, p⟩
      · simp only [not_exists] at x
        have : ∀ n, c.gen n = .bot := fun n =>
          match h : c.gen n with
          | .obj v => False.elim $ x n v h
          | .bot => rfl
        refine ⟨⟨[.bot], .cons (fun _ x => by cases x) .nil, ?_, ?_⟩, .intro⟩
        <;> simp_all
    ⟨Lub.finite w, .intro⟩
