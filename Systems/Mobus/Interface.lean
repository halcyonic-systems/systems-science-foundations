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

/-! ## Interfaces Carry Flow (the converse of bipartite) -/

/-- Every interface carries at least one flow, stated over a bare edge set.

    `IsBipartiteFlow` quantifies over EDGES: every boundary-crossing flow lands
    on an interface. It says nothing about interfaces that carry no flow, so a
    boundary may declare interfaces that do nothing. This predicate is the
    missing converse, quantifying over INTERFACES.

    Mobus's definition of an interface is functional, not positional —
    interfaces are "components that transport flows across the boundary"
    (§4.3), and in Listing 4.2 every `<interface>` carries a mandatory
    `<recievesFrom>` or `<exportsTo>` naming an environmental source or sink.
    An interface with no flow is not expressible in his own description
    language: its `type` (RECEIVES / EXPORTS / hybrid) IS its flow direction. -/
def InterfacesCarryEdges {α : Type*} {κ : Type*}
    (edges : Set (FlowEdge α κ)) (I : Set α) : Prop :=
  ∀ i ∈ I, ∃ e ∈ edges, i = e.source ∨ i = e.target

/-- `InterfacesCarryEdges` on the edge set of a flow network. For external
    flows (G): every interface component is an endpoint of some external flow. -/
def InterfacesCarryFlow {α : Type*} {κ : Type*}
    (net : FlowNetwork α κ) (I : Set α) : Prop :=
  InterfacesCarryEdges net.edges I

/-- An empty interface set carries flow vacuously. This is what keeps the
    degenerate system (no environment, no boundary) constructible: a system
    with no external flows must declare no interfaces, which it already does. -/
theorem interfacesCarryFlow_empty {α : Type*} {κ : Type*}
    (net : FlowNetwork α κ) : InterfacesCarryFlow net (∅ : Set α) :=
  fun _ hi => absurd hi (Set.notMem_empty _)

/-- Interfaces that carry flow are nodes of the flow network. This is the
    payoff: the converse turns `externalFlows_nodes` from a one-way containment
    into a statement with content on the interface side. -/
theorem interfacesCarryFlow_sub_nodes {α : Type*} {κ : Type*}
    (net : FlowNetwork α κ) (I : Set α)
    (h : InterfacesCarryFlow net I) : I ⊆ net.nodes := by
  intro i hi
  obtain ⟨e, he, hsrc | htgt⟩ := h i hi
  · exact hsrc ▸ (net.edges_on e he).1
  · exact htgt ▸ (net.edges_on e he).2

/-- Contrapositive: a declared interface that no external flow touches cannot
    exist. This is the statement the current formalization is missing. -/
theorem no_flowless_interface {α : Type*} {κ : Type*}
    (net : FlowNetwork α κ) (I : Set α)
    (h : InterfacesCarryFlow net I) (i : α) (hi : i ∈ I)
    (hno : ∀ e ∈ net.edges, i ≠ e.source ∧ i ≠ e.target) : False := by
  obtain ⟨e, he, hsrc | htgt⟩ := h i hi
  · exact (hno e he).1 hsrc
  · exact (hno e he).2 htgt

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
