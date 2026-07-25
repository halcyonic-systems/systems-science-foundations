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

/-! ## Non-Vacuity of the Converse (SSF #31)

  The ninth `MobusSystem` field, `interfaces_carry_flow`, is only worth
  carrying if it is INDEPENDENT of the eight constraints that preceded it.
  If the other eight implied it, a green build would prove nothing — the
  field would be decoration and every theorem resting on it would be
  restating what was already true.

  This section settles that with a separating instance: concrete data
  satisfying all five structural coherence constraints of the pre-#31
  `MobusSystem` (plus both `FlowNetwork` invariants on both networks) and
  failing `InterfacesCarryFlow` alone.

  FORM. The witness is stated at the level of the constraints rather than
  as a `MobusSystem` value, because a `MobusSystem` value cannot exhibit
  the failure: the ninth field is part of the structure, so any inhabitant
  satisfies it by construction. Exhibiting the failure inside the type
  would require a duplicate eight-field structure — a second definition of
  the ontology's central object, kept in sync by hand. Restating the five
  constraints against concrete data is the same fact without that cost.
  The fields dropped in the restatement are exactly the ones with no
  structural role: `transforms`, `history`, `timeScale` are parametric and
  unconstrained, and `environment.objects` is literally a bare `Set α`
  (milieu is opaque and enters no constraint).

  DOES NOT COUNT (pre-registered):
  - the degenerate empty system (no edges at all), which would leave open
    whether the converse only bites when nothing flows — hence the witness
    below has a live external flow and a real interface carrying it
  - an added hypothesis that assumes part of the claim
  - a new axiom bridging the gap
-/

namespace InterfaceConverseSeparation

/-- The one environmental object. -/
def envObjects : Set ℕ := {1}

/-- Two components, `0` and `2`. -/
def components : Set ℕ := {0, 2}

/-- Both components are declared interfaces — but only `0` carries a flow.
    `2` is the flowless interface: declared to transport across the
    boundary, touched by no external edge. -/
def interfaces : Set ℕ := {0, 2}

/-- The single external flow: environmental object `1` sends to interface
    `0`. This edge is what makes the witness non-degenerate — the system
    genuinely exchanges with its environment. -/
def liveEdge : FlowEdge ℕ ℕ := ⟨1, 0, 1⟩

/-- G: one boundary-crossing flow, `1 → 0`. Node `2` never appears. -/
def externalFlows : FlowNetwork ℕ ℕ where
  nodes := {0, 1}
  edges := {liveEdge}
  -- why: `e ∈ {liveEdge}` is *definitionally* `e = liveEdge` (Set singleton is
  -- `{b | b = a}`), and `n ∈ {0, 1}` is `n = 0 ∨ n ∈ {1}`. Working through defeq
  -- keeps this section inside the file's own thin import closure.
  edges_on := by
    intro e he
    have he' : e = liveEdge := he
    subst he'
    exact ⟨Or.inr rfl, Or.inl rfl⟩
  no_self_loops := by
    intro e he
    have he' : e = liveEdge := he
    subst he'
    exact Nat.one_ne_zero

/-- N: the internal network on both components, no internal edges.
    Internal structure plays no part in the separation. -/
def internalNetwork : FlowNetwork ℕ ℕ where
  nodes := components
  edges := ∅
  edges_on := by intro e he; exact absurd he (Set.notMem_empty e)
  no_self_loops := by intro e he; exact absurd he (Set.notMem_empty e)

/-- B: boundary properties are irrelevant here, so `π := Unit`. -/
def boundary : MobusBoundary ℕ Unit := ⟨(), interfaces⟩

/-! ### The five pre-#31 constraints all hold -/

/-- `network_components`: N's nodes are exactly C. -/
theorem network_components : internalNetwork.nodes = components := rfl

/-- `disjoint`: components and environmental objects share nothing. -/
theorem disjoint_components_env : components ∩ envObjects = ∅ := by
  ext n
  constructor
  · intro h
    exfalso
    have hc : n = 0 ∨ n = 2 := h.1
    have he : n = 1 := h.2
    rcases hc with h0 | h2 <;> omega
  · intro h
    exact absurd h (Set.notMem_empty n)

/-- `interfaces_sub`: every interface is a component. -/
theorem interfaces_sub : boundary.interfaces ⊆ components :=
  fun _ h => h

/-- `bipartite`: the one external edge crosses from environment to
    interface, so `IsBipartiteFlow` holds — with content, not vacuously. -/
theorem bipartite : IsBipartiteFlow externalFlows envObjects boundary.interfaces := by
  intro e he
  have he' : e = liveEdge := he
  subst he'
  exact Or.inl ⟨rfl, Or.inl rfl⟩

/-- `externalFlows_nodes`: G's nodes sit inside O ∪ I. -/
theorem externalFlows_nodes :
    externalFlows.nodes ⊆ envObjects ∪ boundary.interfaces := by
  intro n hn
  have hn' : n = 0 ∨ n = 1 := hn
  rcases hn' with rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

/-! ### …and the ninth fails -/

/-- Interface `2` is an endpoint of no external edge. -/
theorem flowless_interface :
    ∀ e ∈ externalFlows.edges, (2 : ℕ) ≠ e.source ∧ (2 : ℕ) ≠ e.target := by
  intro e he
  have he' : e = liveEdge := he
  subst he'
  -- why: `omega` needs the projections reduced to numerals first, hence `show`.
  exact ⟨by show (2 : ℕ) ≠ 1; omega, by show (2 : ℕ) ≠ 0; omega⟩

/-- THE SEPARATION: this data fails `InterfacesCarryFlow`. -/
theorem not_interfacesCarryFlow :
    ¬ InterfacesCarryFlow externalFlows boundary.interfaces := by
  intro h
  have h2 : (2 : ℕ) ∈ boundary.interfaces := Or.inr rfl
  exact no_flowless_interface externalFlows boundary.interfaces h 2 h2 flowless_interface

end InterfaceConverseSeparation

/-- **The ninth `MobusSystem` field is not implied by the other eight.**

    There is data satisfying every structural constraint the 8-tuple carried
    before SSF #31 — internal nodes equal the components, components disjoint
    from environmental objects, interfaces contained in components, external
    flows bipartite across the boundary, external nodes inside O ∪ I — and
    failing `InterfacesCarryFlow`.

    What this demonstrates: the pre-#31 formalization admitted a boundary
    declaring an interface that transports nothing. In the witness, component
    `2` is declared an interface while no external flow touches it. Nothing in
    the first eight constraints objects, because all of them quantify over
    edges or over containments — none quantifies over interfaces. Mobus's
    definition is functional (§4.3, Listing 4.2: every `<interface>` carries a
    mandatory `<recievesFrom>`/`<exportsTo>`), so a flowless interface is not
    writable in his description language but WAS constructible in ours.
    `interfaces_carry_flow` is precisely what rules it out, and this theorem
    is the proof that it does work no other field was already doing.

    Note the witness is not the degenerate empty system: it has a live
    external flow `1 → 0` through a genuine interface. The constraint bites
    in systems that really do exchange with their environment. -/
theorem interface_converse_independent :
    ∃ (C O : Set ℕ) (N G : FlowNetwork ℕ ℕ) (B : MobusBoundary ℕ Unit),
      N.nodes = C ∧
      C ∩ O = ∅ ∧
      B.interfaces ⊆ C ∧
      IsBipartiteFlow G O B.interfaces ∧
      G.nodes ⊆ O ∪ B.interfaces ∧
      ¬ InterfacesCarryFlow G B.interfaces :=
  ⟨InterfaceConverseSeparation.components,
   InterfaceConverseSeparation.envObjects,
   InterfaceConverseSeparation.internalNetwork,
   InterfaceConverseSeparation.externalFlows,
   InterfaceConverseSeparation.boundary,
   InterfaceConverseSeparation.network_components,
   InterfaceConverseSeparation.disjoint_components_env,
   InterfaceConverseSeparation.interfaces_sub,
   InterfaceConverseSeparation.bipartite,
   InterfaceConverseSeparation.externalFlows_nodes,
   InterfaceConverseSeparation.not_interfacesCarryFlow⟩

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
