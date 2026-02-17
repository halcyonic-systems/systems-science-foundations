/-
  Systems/Mobus/Interface.lean
  External flow graph: bipartite structure connecting environment to boundary

  Formalizes the revised G network from Mobus's book-revisions:
    G = ⟨o_i ∈ O, c_j ∈ C⟩
  where edges connect environmental objects O to interface components I ⊆ C.

  Original Eq. 4.5 used a bipartite graph with separate Src and Snk sets.
  The revision unifies these into O, since "many objects in a system's
  environment may be both sources and sinks simultaneously." Edge direction
  determines whether an object is a source, sink, or both.

  DESIGN: The bipartite property is a predicate on FlowNetwork, not a
  separate type. This lets MobusSystem carry a single FlowNetwork for G
  with a proof that it satisfies the bipartite constraint. The key payoff:
  bipartite external flows automatically imply BoundaryComplete from
  Boundary.lean — the bridge theorem is free.
-/

import Systems.Mobus.FlowNetwork
import Systems.Mobus.Boundary

namespace Systems

/-! ## Bipartite Flow Property -/

/-- A flow network is bipartite between sets A and B: every edge crosses
    from one side to the other. No edge is internal to either side.

    For external flows (G): A = environment objects, B = interface components.
    The bipartite property captures "every flow crosses the boundary." -/
def IsBipartiteFlow {α : Type*} {κ : Type*}
    (net : FlowNetwork α κ) (A B : Set α) : Prop :=
  ∀ e ∈ net.edges,
    (e.source ∈ A ∧ e.target ∈ B) ∨ (e.source ∈ B ∧ e.target ∈ A)

/-! ## Bipartite Implies Boundary Complete -/

/-- Bipartite external flows automatically satisfy boundary completeness.
    If every edge crosses between envObjects and interfaces, then no
    non-interface, non-environment node appears in any edge.

    This is the bridge theorem: the graph-theoretic property (bipartite)
    implies the systems-theoretic property (boundary mediates all
    interaction). -/
theorem bipartite_implies_boundary_complete {α : Type*} {κ : Type*} {π : Type*}
    (boundary : MobusBoundary α π)
    (flows : FlowNetwork α κ)
    (envObjects : Set α)
    (hbp : IsBipartiteFlow flows envObjects boundary.interfaces) :
    BoundaryComplete boundary flows envObjects := by
  intro e he
  have h := hbp e he
  constructor
  · intro hne
    rcases h with ⟨hs, _⟩ | ⟨hs, _⟩
    · exact absurd hs hne
    · exact hs
  · intro hne
    rcases h with ⟨_, ht⟩ | ⟨_, ht⟩
    · exact ht
    · exact absurd ht hne

/-! ## Environmental Object Classification -/

/-- Environmental sources: objects that send flows into the system.
    An object is a source if it has at least one outgoing edge to an
    interface component.

    Mobus book-revisions: "the flow directions (arrows) determining if
    an object is just a source or a sink or both." -/
def EnvSources {α : Type*} {κ : Type*}
    (flows : FlowNetwork α κ) (envObjects : Set α) : Set α :=
  {o ∈ envObjects | (flows.successors o).Nonempty}

/-- Environmental sinks: objects that receive flows from the system. -/
def EnvSinks {α : Type*} {κ : Type*}
    (flows : FlowNetwork α κ) (envObjects : Set α) : Set α :=
  {o ∈ envObjects | (flows.predecessors o).Nonempty}

/-- Environmental objects that are both sources and sinks.
    Mobus book-revisions: "many objects in a system's environment may be
    both sources, of flows, and sinks, receiving flows." This motivated
    the revision from separate Src/Snk sets to unified O. -/
def EnvDual {α : Type*} {κ : Type*}
    (flows : FlowNetwork α κ) (envObjects : Set α) : Set α :=
  EnvSources flows envObjects ∩ EnvSinks flows envObjects

/-- Sources are environmental objects. -/
theorem envSources_sub {α : Type*} {κ : Type*}
    (flows : FlowNetwork α κ) (envObjects : Set α) :
    EnvSources flows envObjects ⊆ envObjects :=
  fun _ h => h.1

/-- Sinks are environmental objects. -/
theorem envSinks_sub {α : Type*} {κ : Type*}
    (flows : FlowNetwork α κ) (envObjects : Set α) :
    EnvSinks flows envObjects ⊆ envObjects :=
  fun _ h => h.1

/-! ## Bipartite Edge Direction -/

/-- In a bipartite flow with disjoint sides, edges from environmental
    objects always target interface components.
    Requires disjointness: no thing is both an environmental object
    and an interface component. -/
theorem bipartite_env_source_targets_interface {α : Type*} {κ : Type*}
    (flows : FlowNetwork α κ) (envObjects interfaces : Set α)
    (hbp : IsBipartiteFlow flows envObjects interfaces)
    (hdisj : envObjects ∩ interfaces = ∅) :
    ∀ e ∈ flows.edges, e.source ∈ envObjects → e.target ∈ interfaces := by
  intro e he hsrc
  rcases hbp e he with ⟨_, ht⟩ | ⟨hs, _⟩
  · exact ht
  · exfalso
    have := Set.mem_empty_iff_false e.source
    rw [← hdisj] at this
    exact this.mp ⟨hsrc, hs⟩

/-- In a bipartite flow with disjoint sides, edges into environmental
    objects always come from interface components. -/
theorem bipartite_env_sink_sources_interface {α : Type*} {κ : Type*}
    (flows : FlowNetwork α κ) (envObjects interfaces : Set α)
    (hbp : IsBipartiteFlow flows envObjects interfaces)
    (hdisj : envObjects ∩ interfaces = ∅) :
    ∀ e ∈ flows.edges, e.target ∈ envObjects → e.source ∈ interfaces := by
  intro e he htgt
  rcases hbp e he with ⟨_, ht⟩ | ⟨hs, _⟩
  · -- Case: source ∈ env, target ∈ interfaces — but target ∈ env too
    exfalso
    have : e.target ∈ envObjects ∩ interfaces := ⟨htgt, ht⟩
    rw [hdisj] at this
    exact this
  · exact hs

end Systems
