import Mathlib.Data.Nat.PSub

namespace ConcDisSys

inductive Connective e ts (nodes : N → ℕ → Set E) : Prop
  | emittedBefore (hlt : prev < ts) (x : e ∈ nodes node prev)
  | uniqueNow (curr : e ∈ nodes node ts) (unique : ∀ node' ≠ node, e ∉ nodes node' ts)
  | notEmitted (p : ∀ node, e ∉ nodes node ts)

-- This is a very uncomputable definition, optimally we would be using Σ' over ∃
-- since it would let us elim into Type but sadly we are unable to do this
structure Network : Type 1 :=
  -- The amout of nodes
  -- The type of events
  E : Type
  N : Type

  -- Nodes are a collection of functions that at every timestamp can possibly
  -- emit some set of events
  nodes : N → ℕ → Set E

  -- Events are uniquely emitted by a single node. Following this another node
  -- can re-emit said event to show it happened later but some finite amount
  -- of time must have passed.
  connective : ∀ e ts, Connective e ts nodes

  -- Every event must occur at least once
  eventSaturation : ∀ e, ∃ ts node, e ∈ nodes node ts

def FirstOccurence {nw : Network} (e : nw.E) (ts : ℕ) : Prop :=
  (∃ node, e ∈ nw.nodes node ts) ∧
  ∀ prev < ts, ∀ nodes, e ∉ nw.nodes nodes prev

def FirstOccurence.unique
    (f1 : FirstOccurence e t1)
    (f2 : FirstOccurence e t2)
    : t1 = t2 :=
  match h : compare t1 t2 with
  | .eq => Nat.compare_eq_eq.mp h
  | .lt => by
    rw [Nat.compare_eq_lt] at h
    exact False.elim $ f2.2 _ h f1.1.choose f1.1.choose_spec
  | .gt => by
    rw [Nat.compare_eq_gt] at h
    exact False.elim $ f1.2 _ h f2.1.choose f2.1.choose_spec

def extractFirstOccurence
    {nw : Network} {e : nw.E}
    (end_nd : nw.N) (end_ts : ℕ)
    (p : e ∈ nw.nodes end_nd end_ts)
    (current_v : ℕ)
    (hlt : current_v ≤ end_ts)
    (ind_ih : ∀ t < current_v, ∀ nd, e ∉ nw.nodes nd t)
    : Exists (FirstOccurence e) :=
  match nw.connective e current_v with
  | .emittedBefore plt emitted => False.elim (ind_ih _ plt _ emitted)
  | .uniqueNow isEmitted _ =>
    ⟨current_v, ⟨⟨_, isEmitted⟩, ind_ih⟩⟩
  | .notEmitted cont =>
    if h' : end_ts = current_v then by
      subst h'
      exact False.elim (cont _ p)
    else
      extractFirstOccurence end_nd end_ts p current_v.succ (by omega) (fun t h =>
        if h : t = current_v then by
          subst h
          exact cont
        else ind_ih t (by omega))
termination_by end_ts - current_v
decreasing_by
· simp_wf
  omega

def hasFirstOccurence {nw : Network} (e : nw.E) : Exists (FirstOccurence e) := 
  let ⟨ts, nd, p⟩ := nw.eventSaturation e
  extractFirstOccurence nd ts p 0 (Nat.zero_le ts) (fun _ v => by contradiction)

/-- info: 'ConcDisSys.hasFirstOccurence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hasFirstOccurence

def Network.happensBefore {nw : Network} (e1 e2 : nw.E) : Prop :=
  ∃ z, ∃ n > 0, FirstOccurence e1 z ∧ FirstOccurence e2 (z + n)

abbrev Network.concurrent {nw : Network} (e1 e2 : nw.E) : Prop :=
  (¬happensBefore e1 e2) ∧ (¬happensBefore e2 e1)

namespace Network

variable (nw : Network)

set_option quotPrecheck false in section
scoped infixl:50 "≺" => nw.happensBefore
scoped infixl:50 "∥" => nw.concurrent
end

-- ########################################################################
-- ################################ Ex 8 ##################################
-- ########################################################################

theorem happensBefore.irrefl : ¬(a ≺ a) := by
  by_contra h
  rcases h with ⟨w1, diff, pgt, p1, p2⟩
  have := FirstOccurence.unique p1 p2
  omega

theorem happensBefore.trans (h1 : a ≺ b) (h2 : b ≺ c) : a ≺ c := by
  rcases h1 with ⟨w1, diff1, pgt1, p11, p12⟩
  rcases h2 with ⟨w2, diff2, _,    p21, p22⟩
  obtain rfl := FirstOccurence.unique p12 p21
  exists w1
  exists diff1 + diff2
  rw [Nat.add_assoc] at p22
  exact ⟨Nat.add_pos_left pgt1 diff2, p11, p22⟩

-- ########################################################################
-- ################################ Ex 9 ##################################
-- ########################################################################

theorem optionSpace (e1 e2 : nw.E) : e1 ≺ e2 ∨ e2 ≺ e1 ∨ e1 ∥ e2 := by
  have ⟨w1, p1⟩ := hasFirstOccurence e1
  have ⟨w2, p2⟩ := hasFirstOccurence e2
  cases h : compare w1 w2
  <;> simp only [Nat.compare_eq_eq, Nat.compare_eq_gt, Nat.compare_eq_lt] at h
  · refine .inl ⟨w1, w2 - w1, by omega, p1, ?_⟩
    rw [ ←Nat.add_sub_assoc (Nat.le_of_succ_le h) _,
         Nat.add_comm,
         Nat.add_sub_assoc (Nat.le_refl _) _,
         Nat.sub_self,
         Nat.add_zero]
    exact p2

  · subst h
    refine .inr $ .inr ⟨?_, ?_⟩
    <;> rintro ⟨ts, diff, hlt, p1', p2'⟩
    · have eq1 := p1.unique p1'
      have eq2 := p2.unique p2'
      simp_all only [gt_iff_lt, add_right_eq_self, add_zero, Nat.lt_irrefl]
    · have eq1 := p2.unique p1'
      have eq2 := p1.unique p2'
      simp_all only [gt_iff_lt, add_right_eq_self, add_zero, Nat.lt_irrefl]
  · refine .inr $ .inl ⟨w2, w1 - w2, by omega, p2, ?_⟩
    rw [ ←Nat.add_sub_assoc (Nat.le_of_succ_le h) _,
         Nat.add_comm,
         Nat.add_sub_assoc (Nat.le_refl _) _,
         Nat.sub_self,
         Nat.add_zero]
    exact p1

end ConcDisSys.Network

