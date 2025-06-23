structure FSM where
  S : Type
  d : S → Nat → S
  A : S → Prop

inductive Bisim.Invariant (fsm : FSM) (Bisim : fsm.S → fsm.S → Prop) (xv : fsm.S) (yv : fsm.S) : Prop :=
  | step : (fsm.A xv ↔ fsm.A yv) → (∀ c, Bisim (fsm.d xv c) (fsm.d yv c)) → Bisim.Invariant fsm Bisim xv yv

abbrev Bisim.Is (fsm : FSM) (R : fsm.S → fsm.S → Prop) : Prop :=
  ∀ {xv yv}, R xv yv → Bisim.Invariant fsm R xv yv

def Bisim (fsm : FSM) : fsm.S → fsm.S → Prop := fun x y => ∃ R, @Bisim.Is fsm R ∧ R x y

macro "coinduction " "using" P:term "with" ids:(ppSpace colGt ident)+ : tactic =>
  let ids := ids
  `(tactic| (exists $P; constructor; intro $ids*))

theorem bisim_refl : Bisim f a a := by
  refine ⟨Eq, ?_, rfl⟩
  rintro s t rfl
  apply Bisim.Invariant.step
  <;> simp_all

theorem bisim_symm (h : Bisim f a b) : Bisim f b a := by
  rcases h with ⟨rel, relIsBisim, rab⟩
  refine ⟨fun a b => rel b a, ?_, rab⟩
  intro a b holds
  have (⟨curr, next⟩) := relIsBisim holds
  exact .step curr.symm next

theorem Bisim.unfold {f} : Bisim.Is f (Bisim f) := fun ⟨R, h_is, h_Rst⟩ =>
  match h_is h_Rst with
  | .step iff cont => .step iff (⟨R, h_is, cont ·⟩)

-- case principle!
@[elab_as_elim]
def Bisim.casesOn
    {f : FSM} {s t}
    {motive : Bisim f s t → Prop}
    (h : Bisim f s t)
    (step : ∀ {s t}, (f.A s ↔ f.A t)
      → (∀ c, Bisim f (f.d s c) (f.d t c)) → motive h) :
    motive h := by
  have ⟨R, h_is, h_R⟩ := h
  have ⟨h₁, h₂⟩ := h_is h_R
  apply step h₁ (fun c => ⟨R, h_is, h₂ c⟩)

theorem bisim_trans (h_ab : Bisim f a b) (h_bc : Bisim f b c) :
    Bisim f a c := by
  coinduction
    using (fun s t => ∃ u, Bisim f s u ∧ Bisim f u t)
    with s t h_Rst
  · rcases h_Rst with ⟨u, h_su, h_ut⟩
    have ⟨h_su₁, h_su₂⟩ := h_su.unfold
    have ⟨h_ut₁, h_ut₂⟩ := h_ut.unfold
    refine ⟨?_, ?_⟩
    · rw [h_su₁, h_ut₁]
    · intro c; exact ⟨_, h_su₂ c, h_ut₂ c⟩
  · exact ⟨b, h_ab, h_bc⟩
