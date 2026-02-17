/-
  Systems/Mobus/FlowNetwork.lean
  Directed flow networks with parametric capacity

  Formalizes the graph structure underlying Mobus's internal network N
  (Eq. 4.4) and external flow network G (revised Eq. 4.5):

  - Mobus Eq. 4.4: N_{i,l} = ⟨C_{i,l}, L_{i,l}⟩ where L is a set of
    directed edges with capacity cap : C × C → ℝ∞.
  - Book-revisions: G = ⟨o_i ∈ O, c_j ∈ C⟩ (simplified from bipartite
    to general directed graph).

  DESIGN: FlowNetwork is a general directed graph with capacity-labeled
  edges. The capacity type κ is parametric — Mobus uses ℝ∞ but the
  formalization imposes no constraint. This single type serves as the
  basis for both N (internal, nodes = components) and G (external,
  nodes = components ∪ environment objects). The distinction is handled
  at the MobusSystem level, not here.
-/

import Mathlib.Data.Set.Basic

namespace Systems

/-! ## Flow Edges -/

/-- A directed edge in a flow network, carrying a capacity label.
    Mobus §4.3: edge e_{i.k,l} = (c_{i.k,l}, c_{i.o,l}) with capacity
    cap_{i.k,l} : C × C → ℝ∞.

    Parametrized by:
    - α: node type (components, environment objects, etc.)
    - κ: capacity type (ℝ, ℕ, or any type — domain supplies interpretation) -/
structure FlowEdge (α : Type*) (κ : Type*) where
  /-- The source node of the edge -/
  source : α
  /-- The target node of the edge -/
  target : α
  /-- The capacity label on this edge -/
  capacity : κ

/-- The underlying directed pair of a flow edge, forgetting capacity. -/
def FlowEdge.toPair {α : Type*} {κ : Type*} (e : FlowEdge α κ) : α × α :=
  (e.source, e.target)

/-! ## Flow Network -/

/-- A directed flow network: a set of nodes with capacity-labeled edges.

    Mobus Eq. 4.4: N_{i,l} = ⟨C_{i,l}, L_{i,l}⟩
    - C is the node set (components at level l)
    - L is the edge set (directed, with capacity)

    This general structure serves as the basis for both:
    - N (internal network): nodes = components, edges = component interactions
    - G (external flows): nodes = components ∪ environment objects

    Mobus §4.3: "N is generally a flow network through which real substances
    are moving from one node (component) to the next with causal influence." -/
structure FlowNetwork (α : Type*) (κ : Type*) where
  /-- The set of nodes in the network -/
  nodes : Set α
  /-- The set of directed, capacity-labeled edges -/
  edges : Set (FlowEdge α κ)
  /-- Every edge connects nodes in the network -/
  edges_on : ∀ e ∈ edges, e.source ∈ nodes ∧ e.target ∈ nodes
  /-- No self-loops: Mobus §4.3 requires k ≠ o for edge (c_k, c_o) -/
  no_self_loops : ∀ e ∈ edges, e.source ≠ e.target

/-! ## Node Classification -/

/-- The successors of a node: all nodes reachable by a single edge.
    These are the nodes that receive flow from the given node. -/
def FlowNetwork.successors {α : Type*} {κ : Type*}
    (net : FlowNetwork α κ) (a : α) : Set α :=
  {b | ∃ e ∈ net.edges, e.source = a ∧ e.target = b}

/-- The predecessors of a node: all nodes that send flow to it. -/
def FlowNetwork.predecessors {α : Type*} {κ : Type*}
    (net : FlowNetwork α κ) (a : α) : Set α :=
  {b | ∃ e ∈ net.edges, e.source = b ∧ e.target = a}

/-- A source node has outgoing edges but no incoming edges.
    In Mobus's framework, sources in G are environmental objects that
    provide inputs to the system. -/
def FlowNetwork.isSource {α : Type*} {κ : Type*}
    (net : FlowNetwork α κ) (a : α) : Prop :=
  a ∈ net.nodes ∧ (net.successors a).Nonempty ∧ net.predecessors a = ∅

/-- A sink node has incoming edges but no outgoing edges.
    In Mobus's framework, sinks in G are environmental objects that
    receive outputs from the system. -/
def FlowNetwork.isSink {α : Type*} {κ : Type*}
    (net : FlowNetwork α κ) (a : α) : Prop :=
  a ∈ net.nodes ∧ (net.predecessors a).Nonempty ∧ net.successors a = ∅

/-- An internal node has both incoming and outgoing edges.
    In Mobus's framework, these are components that both receive and
    send flows — the processing elements of the system. -/
def FlowNetwork.isInternal {α : Type*} {κ : Type*}
    (net : FlowNetwork α κ) (a : α) : Prop :=
  a ∈ net.nodes ∧ (net.predecessors a).Nonempty ∧ (net.successors a).Nonempty

/-! ## Underlying Relation -/

/-- The underlying directed relation of a flow network, forgetting capacity.
    This connects FlowNetwork to Bunge's structure S_A: the set of
    relations among components. -/
def FlowNetwork.toRelation {α : Type*} {κ : Type*}
    (net : FlowNetwork α κ) : Set (α × α) :=
  {p | ∃ e ∈ net.edges, e.toPair = p}

/-- Every pair in the underlying relation connects nodes in the network. -/
theorem FlowNetwork.toRelation_on {α : Type*} {κ : Type*}
    (net : FlowNetwork α κ) :
    ∀ p ∈ net.toRelation, p.1 ∈ net.nodes ∧ p.2 ∈ net.nodes := by
  intro p ⟨e, he, hep⟩
  rw [FlowEdge.toPair] at hep
  rw [← hep]
  exact net.edges_on e he

/-- The underlying relation has no diagonal elements (from no_self_loops). -/
theorem FlowNetwork.toRelation_irrefl {α : Type*} {κ : Type*}
    (net : FlowNetwork α κ) :
    ∀ p ∈ net.toRelation, p.1 ≠ p.2 := by
  intro p ⟨e, he, hep⟩
  have hsl := net.no_self_loops e he
  rw [← hep]
  simp [FlowEdge.toPair]
  exact hsl

/-! ## Successors and Predecessors are in the Network -/

/-- Every successor of a node in the network is itself in the network. -/
theorem FlowNetwork.successors_sub_nodes {α : Type*} {κ : Type*}
    (net : FlowNetwork α κ) (a : α) :
    net.successors a ⊆ net.nodes := by
  intro b ⟨e, he, _, htgt⟩
  exact htgt ▸ (net.edges_on e he).2

/-- Every predecessor of a node in the network is itself in the network. -/
theorem FlowNetwork.predecessors_sub_nodes {α : Type*} {κ : Type*}
    (net : FlowNetwork α κ) (a : α) :
    net.predecessors a ⊆ net.nodes := by
  intro b ⟨e, he, hsrc, _⟩
  exact hsrc ▸ (net.edges_on e he).1

/-! ## Network Restriction -/

/-- Restrict a flow network to a subset of its nodes.
    Edges are kept only if both endpoints remain in the subset.

    This is useful for extracting internal structure: given a MobusSystem
    with components C and environment O, restricting the total network
    to C gives the internal network N, while restricting to C ∪ O and
    filtering for cross-boundary edges gives G. -/
def FlowNetwork.restrict {α : Type*} {κ : Type*}
    (net : FlowNetwork α κ) (sub : Set α) :
    FlowNetwork α κ where
  nodes := sub
  edges := {e ∈ net.edges | e.source ∈ sub ∧ e.target ∈ sub}
  edges_on := by
    intro e ⟨_, hsrc, htgt⟩
    exact ⟨hsrc, htgt⟩
  no_self_loops := by
    intro e ⟨he, _, _⟩
    exact net.no_self_loops e he

/-- Restricting to the full node set gives back the same edges. -/
theorem FlowNetwork.restrict_full_edges {α : Type*} {κ : Type*}
    (net : FlowNetwork α κ) :
    ∀ e ∈ net.edges, e ∈ (net.restrict net.nodes).edges := by
  intro e he
  have hon := net.edges_on e he
  exact ⟨he, hon.1, hon.2⟩

end Systems
