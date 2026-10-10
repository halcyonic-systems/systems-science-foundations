/-
  Systems/Dynamics/AgentStep.lean
  The agent layer's first obligation — facets#269, ADR 0008 D6.

  `agent_step_is_product`: a circuit whose agents are all deterministic steps as
  ONE deterministic transition on the product of its stock coordinates and its
  agent-memory coordinates, with no new functor. Adding reactive agents does not
  change what kind of thing a run is.

  THE SHAPE. An agent (Mobus ch. 11 Fig. 11.1) reads the stocks, decides a
  command from what it reads and what it remembers, and the stocks step under
  that command; the agent then updates its memory. Three maps, one product:

    decide   : S → M → C        the decision model over the observation and H
    remember : S → M → M        the experiential memory's update (H)
    stepWith : C → S → S        the work processes under the command

  `AgentLayer.step : S × M → S × M` is their composition, read-before-write
  (the command is computed from the pre-tick state), which is exactly the
  phase bert-compose runs at the top of `step_dt` (circuit.rs, `NodeKind::Agent`).
  At the first rung M is `Unit` (purely reactive, no memory); the type is kept
  general because the adaptive-reactive rule (a trace statistic) is the same
  shape with a nontrivial M.

  WHAT IS PROVED. `AgentLayer.transition` TYPECHECKS as
  `Transition (Dynamics.conservationExample (S × M))`, the deterministic
  coalgebra of Transition.lean — the type is the check — and
  `agent_step_is_product` states by `rfl` that its step is the product step.
  The homogeneity constraint of ADR 0008 D2 is the SEPARATING INSTANCE:
  `MarkovAgentLayer` (a dice-rolling decision) typechecks only as the Markov
  coalgebra, and `markov_codomain_ne_deterministic` shows the two codomains
  are different types, so no deterministic typing of the sampling agent
  exists. Mixing the two in one run is the heterogeneous composition the
  Transition.lean header names as the open frontier, and it stays open here.

  NOT CLAIMED. Nothing about agents managing agents (a layered state with two
  time scales — Mobus §12.2.3.3), nothing about H beyond what `M` carries,
  nothing about the conservation ledger (an invariant over trajectories, not a
  kind — Record.lean finding 1). Each is a later obligation with its own name.

  AXIOM-FREE AND CONSERVATIVE. Adds definitions and three results; touches no
  existing theorem. `#print axioms` on the three is recorded at the end.
-/

import Systems.Dynamics.Transition

namespace Systems

/-- An agent layer over stocks `S` with memory `M` and commands `C`: the three
    maps of Mobus's Fig. 11.1 as bert-compose runs them. -/
structure AgentLayer (S M C : Type) where
  /-- The decision model: observation and memory to a command. -/
  decide : S → M → C
  /-- The memory update (H); `fun _ m => m` at the purely reactive rung. -/
  remember : S → M → M
  /-- The work processes under the command: one tick of the stocks. -/
  stepWith : C → S → S

namespace AgentLayer

variable {S M C : Type}

/-- One tick, read-before-write: the command comes from the pre-tick state,
    the stocks step under it, the memory updates from the pre-tick state. -/
def step (al : AgentLayer S M C) : S × M → S × M :=
  fun (s, m) => (al.stepWith (al.decide s m) s, al.remember s m)

/-- The layer as a typed transition: the DETERMINISTIC coalgebra on the product
    carrier. That this definition elaborates is the obligation's first half —
    the step with agents has the `Id` kind, nothing more. -/
def transition (al : AgentLayer S M C) :
    Transition (Dynamics.conservationExample (S × M)) :=
  Transition.deterministicClosed al.step

/-- ADR 0008 D6, `agent_step_is_product`: the typed transition's step IS the
    product step, definitionally. No new functor, no new state shape — the
    stocks' coordinates and the agents' memory coordinates, and the kind stays
    deterministic. -/
theorem agent_step_is_product (al : AgentLayer S M C) (s : S) (m : M) :
    (al.transition).step ((), (s, m)) = ((), al.step (s, m)) := rfl

/-- The purely reactive rung (ADR 0008 D4: Threshold, Proportional, Table): no
    memory, so `M = Unit` and the decision reads the stocks alone. -/
def reactive (decide : S → C) (stepWith : C → S → S) : AgentLayer S Unit C where
  decide := fun s _ => decide s
  remember := fun _ m => m
  stepWith := stepWith

/-- A reactive layer's step on the stocks is the stocks under the decision,
    and the memory coordinate is inert. -/
theorem reactive_step (decide : S → C) (stepWith : C → S → S) (s : S) :
    (reactive decide stepWith).step (s, ()) = (stepWith (decide s) s, ()) := rfl

end AgentLayer

/-! ## The separating instance: a sampling agent is not of this kind -/

/-- An agent whose decision is a Nat-weighted choice among commands — the
    Markov rule of bert-lenses#67, kept out of the first rung by ADR 0008 D2. -/
structure MarkovAgentLayer (S M C : Type) where
  decide : S → M → List (C × Nat)
  remember : S → M → M
  stepWith : C → S → S

namespace MarkovAgentLayer

variable {S M C : Type}

/-- One tick: every weighted command gives a weighted successor. -/
def step (al : MarkovAgentLayer S M C) : S × M → List ((S × M) × Nat) :=
  fun (s, m) => (al.decide s m).map (fun p => ((al.stepWith p.1 s, al.remember s m), p.2))

/-- The sampling layer typechecks as the MARKOV coalgebra and as nothing else
    this file can write: its codomain is `kindCodomain .markov`, a weighted
    list, not a single next state. -/
def transition (al : MarkovAgentLayer S M C) :
    Transition (Dynamics.billMarkovDescriptor (S × M)) :=
  Transition.markovClosed al.step

end MarkovAgentLayer

/-- The two kinds have different codomains, so a sampling agent has no
    deterministic typing and a run mixing the two has no single kind: the
    constraint of ADR 0008 D2 bites. Proof: `Unit` is a subsingleton and
    `List (Unit × Nat)` is not (`[]` and `[((), 0)]` differ), so the types
    cannot be equal. -/
theorem markov_codomain_ne_deterministic :
    kindCodomain .markov Unit ≠ kindCodomain .deterministic Unit := by
  intro h
  have hsub : Subsingleton (kindCodomain .markov Unit) := by
    rw [h]
    exact ⟨fun _ _ => rfl⟩
  have this : ([] : List (Unit × Nat)) = [((), 0)] := @Subsingleton.elim _ hsub _ _
  exact List.cons_ne_nil _ _ this.symm

#print axioms AgentLayer.agent_step_is_product
#print axioms AgentLayer.reactive_step
#print axioms markov_codomain_ne_deterministic

end Systems
