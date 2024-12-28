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

structure FirstOccurenceOnNode {nw : Network} (e : nw.E) (ts : ℕ) (node : nw.N) : Prop :=
  occures : e ∈ nw.nodes node ts
  isFirst : ∀ prev < ts, e ∉ nw.nodes node prev

structure TransmittedAt {nw : Network} (e : nw.E) (ts : ℕ) : Prop :=
  occures : ∃ node, e ∈ nw.nodes node ts
  isFirst : ∀ prev < ts, ∀ nodes, e ∉ nw.nodes nodes prev

theorem TransmittedAt_ex_FirstOccurenceOnNode (h : TransmittedAt e ts)
    : ∃ n, FirstOccurenceOnNode e ts n :=
  ⟨h.occures.choose,
    { occures := h.occures.choose_spec, isFirst := (h.isFirst · · h.occures.choose) }⟩

def TransmittedAt.unique
    (f1 : TransmittedAt e t1)
    (f2 : TransmittedAt e t2)
    : t1 = t2 :=
  match h : compare t1 t2 with
  | .eq => Nat.compare_eq_eq.mp h
  | .lt => by
    rw [Nat.compare_eq_lt] at h
    exact False.elim $ f2.isFirst _ h f1.occures.choose f1.occures.choose_spec
  | .gt => by
    rw [Nat.compare_eq_gt] at h
    exact False.elim $ f1.isFirst _ h f2.occures.choose f2.occures.choose_spec

def extractTransmittedAt
    {nw : Network} {e : nw.E}
    (end_nd : nw.N) (end_ts : ℕ)
    (p : e ∈ nw.nodes end_nd end_ts)
    (current_v : ℕ)
    (hlt : current_v ≤ end_ts)
    (ind_ih : ∀ t < current_v, ∀ nd, e ∉ nw.nodes nd t)
    : Exists (TransmittedAt e) :=
  match nw.connective e current_v with
  | .emittedBefore plt emitted => False.elim (ind_ih _ plt _ emitted)
  | .uniqueNow isEmitted _ =>
    ⟨current_v, ⟨⟨_, isEmitted⟩, ind_ih⟩⟩
  | .notEmitted cont =>
    if h' : end_ts = current_v then by
      subst h'
      exact False.elim (cont _ p)
    else
      extractTransmittedAt end_nd end_ts p current_v.succ (by omega) (fun t h =>
        if h : t = current_v then by
          subst h
          exact cont
        else ind_ih t (by omega))
termination_by end_ts - current_v
decreasing_by
· simp_wf
  omega

def hasTransmittedAt {nw : Network} (e : nw.E) : Exists (TransmittedAt e) := 
  let ⟨ts, nd, p⟩ := nw.eventSaturation e
  extractTransmittedAt nd ts p 0 (Nat.zero_le ts) (fun _ v => by contradiction)

/-- info: 'ConcDisSys.hasTransmittedAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hasTransmittedAt

namespace Network.Behaviour

def Recipient (nw : Network) : Type := nw.E → nw.N

namespace Network

def Reliabale {nw : Network} (r : Recipient nw) : Prop :=
  ∀ event, ∃! ts, event ∈ nw.nodes (r event) ts

end Network

namespace Node

-- To formalize Byzantine behaviour we need to first formalize a 'network
-- protocol'. This is a relatively complex problem but should be doable

structure CrashSet (nw : Network) : Type :=
  crashedNodes : ℕ → Set nw.N
  crashedCannotTransmit : ∀ ts, ∀ n ∈ crashedNodes ts, nw.nodes n ts = {}

-- Crashed nodes never recover
def CrashStop {nw : Network} (cs : CrashSet nw) : Prop :=
  ∀ n ts, n ∈ cs.crashedNodes ts → n ∈ cs.crashedNodes (ts + 1)

end Node

namespace Timing

def ArrivedBy {nw : Network} (e : nw.E) (n : nw.N) (ts : ℕ) : Prop :=
  ∃ ts' ≤ ts, e ∈ nw.nodes n ts'

def Syncronous {nw : Network} (r : Recipient nw) : Prop :=
  ∃ upperBound, ∀ e, ∃ ts, TransmittedAt e ts ∧ ArrivedBy e (r e) (ts + upperBound)

end Network.Behaviour.Timing

