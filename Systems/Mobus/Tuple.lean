/-
  Systems/Mobus/Tuple.lean
  The Mobus 8-tuple: S = ⟨C, N, E, G, B, T, H, Δt⟩

  Assembles the four preceding Mobus modules (FlowNetwork, Environment,
  Boundary, Interface) into a single coherent system structure with
  consistency constraints enforced by the type.

  Book-revisions Eq. 1:
    S_{i,l} = ⟨C, N, E, G, B, T, H, Δt⟩_{i,l}
  where:
    C = components         N = internal network
    E = ⟨O, M⟩ environment   G = external flows
    B = ⟨P, I⟩ boundary     T = transforms
    H = history/knowledge   Δt = time scale

  DESIGN: T, H, Δt are parametric — Mobus describes them informally and
  their content is domain-specific. The structural fields (C, N, E, G, B)
  carry machine-checked coherence constraints: network nodes match
  components, external flows are bipartite across the boundary, interfaces
  are components, and components are disjoint from environment objects.

  Boundary completeness (showcase #3) is NOT an axiom here — it is derived
  from the bipartite constraint via bipartite_implies_boundary_complete.
-/

import Systems.Mobus.FlowNetwork
import Systems.Mobus.Environment
import Systems.Mobus.Boundary
import Systems.Mobus.Interface

namespace Systems

/-! ## The 8-Tuple -/

/-- A Mobus system: the revised 8-tuple S = ⟨C, N, E, G, B, T, H, Δt⟩.

    Type parameters:
    - α: node type (components and environmental objects share this type)
    - κ: capacity type for flow edges (parametric — ℝ, ℕ, or any type)
    - μ: milieu type (ambient environmental variables, opaque)
    - π: boundary property type (opaque — "exact form is still research")
    - τ: transform type (domain-specific processing functions)
    - η: history type (stored knowledge / memory)
    - δ: time scale type (Δt — temporal resolution)

    The first five type parameters (α, κ, μ, π) are structurally active —
    they participate in coherence constraints. The last three (τ, η, δ)
    are carried data with no structural role in the ontology. -/
structure MobusSystem (α : Type*) (κ : Type*) (μ : Type*)
    (π : Type*) (τ : Type*) (η : Type*) (δ : Type*) where

  -- === The 8-tuple fields ===

  /-- C: the set of components at this level.
      Mobus §4.3: C_{i,l} = {(c_{i.k,l}, ...)} -/
  components : Set α

  /-- N: the internal flow network among components.
      Mobus Eq. 4.4: N_{i,l} = ⟨C_{i,l}, L_{i,l}⟩ -/
  internalNetwork : FlowNetwork α κ

  /-- E: the environment ⟨O, M⟩.
      Book-revisions: O = discrete objects, M = opaque milieu. -/
  environment : MobusEnvironment α μ

  /-- G: the external flow network connecting O to interface components.
      Book-revisions: G = ⟨o_i ∈ O, c_j ∈ C⟩, simplified from bipartite. -/
  externalFlows : FlowNetwork α κ

  /-- B: the boundary ⟨P, I⟩.
      Mobus Eq. 4.6: P = boundary properties, I = interface components. -/
  boundary : MobusBoundary α π

  /-- T: transformation functions (domain-specific, parametric). -/
  transforms : τ

  /-- H: history / stored knowledge (domain-specific, parametric). -/
  history : η

  /-- Δt: time scale / temporal resolution (domain-specific, parametric). -/
  timeScale : δ

  -- === Coherence constraints ===

  /-- Internal network nodes are exactly the components.
      Mobus Eq. 4.4: N = ⟨C, L⟩ — the vertex set of N is C. -/
  network_components : internalNetwork.nodes = components

  /-- Components and environment objects are disjoint.
      Mirrors Bunge Def 1.2: C ∩ E = ∅. -/
  disjoint : components ∩ environment.objects = ∅

  /-- Interface components are a subset of components.
      Mobus: interfaces are "components that transport flows across
      the boundary." -/
  interfaces_sub : boundary.interfaces ⊆ components

  /-- External flows are bipartite: every edge crosses between
      environment objects and interface components.
      From this single constraint, boundary completeness follows
      (see boundaryComplete below). -/
  bipartite : IsBipartiteFlow externalFlows environment.objects boundary.interfaces

  /-- External flow nodes are within environment objects ∪ interfaces. -/
  externalFlows_nodes :
    externalFlows.nodes ⊆ environment.objects ∪ boundary.interfaces

  /-- Every interface carries a flow — the converse of `bipartite`.
      `bipartite` quantifies over edges (flow ⟹ interface); this quantifies
      over interfaces (interface ⟹ flow). Without it a boundary may declare
      interfaces that transport nothing, which Mobus's functional definition
      ("components that transport flows across the boundary") forbids. -/
  interfaces_carry_flow :
    InterfacesCarryFlow externalFlows boundary.interfaces

/-! ## Derived Properties -/

/-- Boundary completeness holds for any well-formed MobusSystem.
    This is NOT assumed — it follows from the bipartite constraint.
    Showcase theorem #3: the systems-theoretic property (boundary mediates
    all interaction) is a structural consequence of how G is defined. -/
theorem MobusSystem.boundaryComplete {α κ μ π τ η δ : Type*}
    (sys : MobusSystem α κ μ π τ η δ) :
    BoundaryComplete sys.boundary sys.externalFlows sys.environment.objects :=
  bipartite_implies_boundary_complete sys.boundary sys.externalFlows
    sys.environment.objects sys.bipartite

/-- Interfaces are exactly the component-side nodes of G. `externalFlows_nodes`
    gives G's nodes ⊆ O ∪ I; `interfaces_carry_flow` gives the interface half of
    the reverse containment. Before the converse, `I` and `G` could drift apart
    with only the ⊆ direction holding. -/
theorem MobusSystem.interfaces_sub_externalNodes {α κ μ π τ η δ : Type*}
    (sys : MobusSystem α κ μ π τ η δ) :
    sys.boundary.interfaces ⊆ sys.externalFlows.nodes :=
  interfacesCarryFlow_sub_nodes sys.externalFlows sys.boundary.interfaces
    sys.interfaces_carry_flow

/-- A system with no external flows has no interfaces. The degenerate case:
    an isolated system's boundary declares nothing, rather than declaring
    interfaces that transport nothing. -/
theorem MobusSystem.no_flows_no_interfaces {α κ μ π τ η δ : Type*}
    (sys : MobusSystem α κ μ π τ η δ)
    (h : sys.externalFlows.edges = ∅) : sys.boundary.interfaces = ∅ := by
  ext i
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hi
  obtain ⟨e, he, _⟩ := sys.interfaces_carry_flow i hi
  rw [h] at he
  exact absurd he (Set.notMem_empty e)

/-! ## Total Structure (Bridge Preparation) -/

/-- The total relation: union of internal and external network relations.
    This is the Mobus counterpart of Bunge's structure S_A — the set of
    all relations among components and between components and environment.

    Information loss: capacity labels are discarded by toRelation.
    This is one of two systematic losses in the Mobus→Bunge projection
    (the other being milieu in Environment.toBungeEnvironment). -/
def MobusSystem.totalRelation {α κ μ π τ η δ : Type*}
    (sys : MobusSystem α κ μ π τ η δ) : Set (α × α) :=
  sys.internalNetwork.toRelation ∪ sys.externalFlows.toRelation

/-- Every pair in the total relation connects things in
    components ∪ environment objects. This is the Mobus counterpart of
    Bunge's constraint that S_A is defined on C ∪ E. -/
theorem MobusSystem.totalRelation_on {α κ μ π τ η δ : Type*}
    (sys : MobusSystem α κ μ π τ η δ) :
    ∀ p ∈ sys.totalRelation,
      p.1 ∈ sys.components ∪ sys.environment.objects ∧
      p.2 ∈ sys.components ∪ sys.environment.objects := by
  intro p hp
  rcases hp with hi | he
  · -- Internal edge: both endpoints in components (= network nodes)
    have hon := sys.internalNetwork.toRelation_on p hi
    rw [sys.network_components] at hon
    exact ⟨Set.mem_union_left _ hon.1, Set.mem_union_left _ hon.2⟩
  · -- External edge: endpoints in env objects ∪ interfaces ⊆ env ∪ components
    have hon := sys.externalFlows.toRelation_on p he
    constructor
    · rcases Set.mem_of_subset_of_mem sys.externalFlows_nodes hon.1 with h | h
      · exact Set.mem_union_right _ h
      · exact Set.mem_union_left _ (sys.interfaces_sub h)
    · rcases Set.mem_of_subset_of_mem sys.externalFlows_nodes hon.2 with h | h
      · exact Set.mem_union_right _ h
      · exact Set.mem_union_left _ (sys.interfaces_sub h)

/-- Internal network edges only connect components (not environment). -/
theorem MobusSystem.internal_edges_in_components {α κ μ π τ η δ : Type*}
    (sys : MobusSystem α κ μ π τ η δ) :
    ∀ p ∈ sys.internalNetwork.toRelation,
      p.1 ∈ sys.components ∧ p.2 ∈ sys.components := by
  intro p hp
  have hon := sys.internalNetwork.toRelation_on p hp
  rw [sys.network_components] at hon
  exact hon

end Systems
