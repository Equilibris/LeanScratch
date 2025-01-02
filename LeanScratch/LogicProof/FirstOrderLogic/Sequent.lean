import LeanScratch.LogicProof.FirstOrderLogic.Formula
import LeanScratch.LogicProof.FirstOrderLogic.Valuation
import LeanScratch.Fin2

namespace FOL

inductive Sequent {TNm : Type} {PNm : Type} {TA : TNm → ℕ} {PA : PNm → ℕ} :
    List (Formula TA PA) → List (Formula TA PA) → Type
  -- This has the same effect as using sets
  | cycleL : Sequent (Γ ++ [hd]) Δ
      → Sequent ([hd] ++ Γ) Δ
  | cycleR : Sequent Γ (Δ ++ [hd])
      → Sequent Γ ([hd] ++ Δ)

  | wL : Sequent Γ Δ
      → Sequent (a :: Γ) Δ
  | wR : Sequent Γ Δ
      → Sequent Γ (a :: Δ)
  | cL : Sequent (a :: a :: Γ) Δ
      → Sequent (a :: Γ) Δ
  | cR : Sequent Γ (a :: a :: Δ)
      → Sequent Γ (a :: Δ)

  | triv : Sequent (a :: Γ) (a :: Δ)

  | negL : Sequent Γ (a :: Δ)
      →  Sequent (.neg a :: Γ) Δ
  | negR : Sequent (a :: Γ) Δ
      →  Sequent Γ (.neg a :: Δ)

  | conjL : Sequent (a :: b :: Γ) Δ
      → Sequent (.conj a b :: Γ) Δ
  | conjR : Sequent Γ (a :: Δ) → Sequent Γ (b :: Δ)
      → Sequent Γ (.conj a b :: Δ)

  | disjL : Sequent (a :: Γ) Δ → Sequent (b :: Γ) Δ
      → Sequent (.disj a b :: Γ) Δ
  | disjR : Sequent Γ (a :: b :: Δ)
      → Sequent Γ (.disj a b :: Δ)

  | impL : Sequent Γ (a :: Δ) → Sequent (b :: Γ) Δ
      → Sequent (.imp a b :: Γ) Δ
  | impR : Sequent (a :: Γ) (b :: Δ)
      → Sequent Γ (.imp a b :: Δ)

  | iffR  : Sequent (a :: Γ) (b :: Δ) →
            Sequent (b :: Γ) (a :: Δ)
      → Sequent Γ (.iff a b :: Δ)

  | iffL  : Sequent Γ (a :: Δ) → Sequent (b :: Γ) Δ
      → Sequent (.iff a b :: Γ) Δ
  | iffL' : Sequent (.iff b a :: Γ) Δ
      → Sequent (.iff a b :: Γ) Δ

  | cut : Sequent Γ (a :: Δ) → Sequent (a :: Γ) Δ
      → Sequent Γ Δ

  | univL t : Sequent (a t :: Γ) Δ
      → Sequent (.univ a :: Γ) Δ
  | univR : ((x : _) → Sequent Γ (a x :: Δ))
      → Sequent Γ (.univ a :: Δ)

  | exisL : ((x : _) → Sequent (a x :: Γ) Δ)
      → Sequent (.exis a :: Γ) Δ
  | exisR t : Sequent Γ (a t :: Δ)
      → Sequent Γ (.exis a :: Δ)

inductive Holding (v : Valuation TA PA) : List (Formula TA PA) → Type
  | nil : Holding v []
  | cons : hd.denote v → Holding v tl → Holding v (hd :: tl)

def Holding.append {v : Valuation TA PA} : Holding v a → Holding v b → Holding v (a ++ b)
  | .cons hd tl, b => .cons hd $ tl.append b | .nil, b => b

instance : HAppend (Holding v a) (Holding v b) (Holding v (a ++ b)) := ⟨Holding.append⟩

-- I include a proof of this here to make sure we can keep a focus on this
-- only holding based of the underlying assumption on (in our case choice,
-- but in practice) LEM.
  /- imp_iff_not_or -/
private theorem imp_eq_not_or : (a → b) ↔ (¬a ∨ b) := ⟨
  fun f => Classical.byContradiction
    (let ⟨nna, nb⟩ := not_or.mp ·
    nb (f $ Classical.not_not.mp nna)),
  fun | .inl na, a => (na a).elim | .inr b, _ => b⟩

-- Once again very non-constructive
example {P : α → Prop} : (∀ x, (P x ∨ Q)) → (∀ x, P x) ∨ Q := by
  exact forall_or_right.mp
  /- intro h -/
  /- by_contra! -/
  /- rcases this with ⟨⟨w, p⟩, v⟩ -/
  /- specialize h w -/
  /- rcases h with (h|h) -/
  /- · exact p h -/
  /- · exact v h -/

private def Sequent.transform.pullOut
    {TA : TNm → Nat} {PA : PNm → Nat} {v : Valuation TA PA}
    {tl : List (Formula TA PA)} {hd : Formula TA PA}
    (h : hd.denote v ∨ ∃ idx : Fin tl.length, tl[idx].denote v)
  : ∃ idx : Fin ((hd :: tl).length), Formula.denote v (hd :: tl)[idx] :=
  match h with
  | .inl p => ⟨⟨0, Nat.zero_lt_succ _⟩, p⟩
  | .inr ⟨idx, p⟩ => ⟨idx.succ, p⟩

/-- Proves the correctness of the Sqeuent construct -/
def Sequent.transform {TA : TNm → Nat} {PA : PNm → Nat} {Γ Δ : List (Formula TA PA)} (v : Valuation TA PA)
    : Sequent Γ Δ → Holding v Γ → ∃ (idx : Fin (Δ.length)), Δ[idx].denote v
  | .cycleL s, .cons hd tl =>
    s.transform v (tl ++ Holding.cons hd .nil)
  | .cycleR (Δ := Δ) s, k =>
    have ⟨⟨idx, hlt⟩, holds⟩ := s.transform v k
    ⟨⟨if idx = Δ.length then 0 else idx.succ, by
      split
      · simp only [List.singleton_append, List.length_cons, Nat.zero_lt_succ]
      · simp only [Nat.succ_eq_add_one, List.singleton_append, List.length_cons,
          Nat.add_lt_add_iff_right]
        rw [List.length_append, List.length_singleton] at hlt
        omega ⟩, by
      split
      next h =>
        subst h
        simp_all
      next h =>
        have : idx < Δ.length := by
          simp only [List.length_append, List.length_singleton] at hlt
          omega
        simp_all [List.getElem_append_left Δ [_] this]
      ⟩
  | .wL s, .cons hd tl => s.transform v tl
  | .wR s, k =>
    have ⟨⟨idx, hlt⟩, holds⟩ := s.transform v k
    ⟨⟨idx.succ, Nat.add_lt_add_iff_right.mpr hlt⟩, holds⟩
  | .cL s, .cons hd tl => s.transform v (.cons hd $ .cons hd $ tl)
  | .cR s, k =>
    have ⟨⟨idx, hlt⟩, holds⟩ := s.transform v k
    ⟨
      ⟨idx.pred, by simp only [List.length_cons, Nat.pred_eq_sub_one] at hlt ⊢; omega⟩,
      by
      simp only [List.length_cons, Fin.getElem_fin, Nat.pred_eq_sub_one] at hlt holds ⊢
      cases idx <;> exact holds
    ⟩

  | .triv, .cons hd tl => ⟨⟨0, Nat.zero_lt_succ _⟩, hd⟩

  | .negL s, .cons hd tl =>
    match s.transform v tl with
    | ⟨⟨0, _⟩, p⟩ => (hd p).elim
    | ⟨⟨n+1, hlt⟩, holds⟩ =>
      ⟨
        ⟨n, Nat.add_lt_add_iff_right.mp hlt⟩,
        by simp_all
      ⟩
  | .negR (a := a) s, k => by
    by_cases h : a.denote v
    · have ⟨⟨idx, hlt⟩, v⟩:= s.transform v $ .cons h k
      exact ⟨⟨idx.succ, Nat.add_lt_add_iff_right.mpr hlt⟩, v⟩
    · exact ⟨⟨0, Nat.zero_lt_succ _⟩, h⟩
  | .conjL s, .cons ⟨a, b⟩ tl =>
    s.transform v $ .cons a $ .cons b tl
  | .conjR a b, k =>
    match a.transform v k, b.transform v k with
    | ⟨⟨0, _⟩, pa⟩, ⟨⟨0,_⟩, pb⟩ => ⟨⟨0, Nat.zero_lt_succ _⟩, ⟨pa, pb⟩⟩
    | ⟨⟨n+1, hlt⟩, p⟩, _ | _, ⟨⟨n+1, hlt⟩, p⟩ => ⟨⟨n+1, hlt⟩, p⟩
  | .disjL a _, .cons (.inl pa) tl => a.transform v $ .cons pa tl
  | .disjL _ b, .cons (.inr pb) tl => b.transform v $ .cons pb tl
  | .disjR s, k =>
    match s.transform v k with
    | ⟨⟨0, _⟩, p⟩ => ⟨⟨0, Nat.zero_lt_succ _⟩, .inl p⟩
    | ⟨⟨1, _⟩, p⟩ => ⟨⟨0, Nat.zero_lt_succ _⟩, .inr p⟩
    | ⟨⟨n+2, hlt⟩, p⟩ => ⟨⟨n+1, Nat.add_lt_add_iff_right.mpr $ Nat.add_lt_add_iff_right.mp hlt⟩, p⟩
  | .impL a b, .cons hd tl =>
    match a.transform v tl with
    | ⟨⟨0, _⟩, p⟩ => b.transform v $ .cons (hd p) tl
    | ⟨⟨n+1, hlt⟩, p⟩ => ⟨⟨n, Nat.add_lt_add_iff_right.mp hlt⟩, p⟩
  | .iffL a b, .cons hd tl =>
    match a.transform v tl with
    | ⟨⟨0, _⟩, p⟩ => b.transform v $ .cons (hd.mp p) tl
    | ⟨⟨n+1, hlt⟩, p⟩ => ⟨⟨n, Nat.add_lt_add_iff_right.mp hlt⟩, p⟩
  | .iffL' s, .cons hd tl => s.transform v $ .cons hd.symm tl
  | .cut a b, k =>
    match a.transform v k with
    | ⟨⟨0, _⟩, p⟩ => b.transform v $ .cons p k
    | ⟨⟨n+1, hlt⟩, p⟩ => ⟨⟨n, Nat.add_lt_add_iff_right.mp hlt⟩, p⟩
  | .univL a b, .cons hd tl =>
    b.transform v $ .cons (hd a) tl
  | .exisL s, .cons ⟨w, p⟩ tl => (s w).transform v $ .cons p tl
  | .exisR a b, k =>
    match b.transform v k with
    | ⟨⟨0, _⟩, p⟩ => ⟨⟨0, Nat.zero_lt_succ _⟩, ⟨a, p⟩⟩
    | ⟨⟨n+1, hlt⟩, p⟩ => ⟨⟨n+1, hlt⟩, p⟩

  -- The following 3 cases are all extremely non-constructive so be aware.

  | .impR (a := a) s, k => by
    -- I feel this is using AxK quite strongly.
    -- Don't think this would be possible in `Type`.
    -- Or more accuratly I think the denotation would have to be `Decidable`.
    by_cases h : a.denote v
    · match s.transform v $ .cons h k with
      | ⟨⟨0, _⟩, p⟩ => exact ⟨⟨0, Nat.zero_lt_succ _⟩, fun _ => p⟩
      | ⟨⟨n+1, hlt⟩, p⟩ => exact ⟨⟨n+1, hlt⟩, p⟩
    · exact ⟨⟨0, Nat.zero_lt_succ _⟩, imp_eq_not_or.mpr (.inl h)⟩
  | .iffR (a := a) (b := b) sa sb, k => by
    by_cases ha : a.denote v
    <;> by_cases hb : b.denote v
    · exact ⟨⟨0, Nat.zero_lt_succ _⟩, ⟨fun _ => hb, fun _ => ha⟩⟩
    · match sa.transform v $ .cons ha k with
      | ⟨⟨0, _⟩, p⟩ => exact (hb p).elim
      | ⟨⟨n+1, hlt⟩, p⟩ => exact ⟨⟨n+1, hlt⟩, p⟩
    · match sb.transform v $ .cons hb k with
      | ⟨⟨0, _⟩, p⟩ => exact (ha p).elim
      | ⟨⟨n+1, hlt⟩, p⟩ => exact ⟨⟨n+1, hlt⟩, p⟩
    · exact ⟨⟨0, Nat.zero_lt_succ _⟩, iff_iff_and_or_not_and_not.mpr $ .inr ⟨ha, hb⟩⟩
  | .univR s, k =>
    Sequent.transform.pullOut $ forall_or_right.mp
      (match s · |>.transform v k with
      | ⟨⟨0, _⟩, p⟩ => .inl p
      | ⟨⟨n+1, hlt⟩, p⟩ => .inr ⟨⟨n, Nat.add_lt_add_iff_right.mp hlt⟩, p⟩)

/-- info: 'FOL.Sequent.transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Sequent.transform

