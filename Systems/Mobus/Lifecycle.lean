/-
  Systems/Mobus/Lifecycle.lean
  Lawful change for the Mobus 8-tuple.

  Well-formedness is deliberately reified over raw data. This avoids the
  vacuous closure statement obtained by taking both the source and target to
  be `MobusSystem`, whose structure fields already contain every law.
-/

import Systems.Mobus.Tuple
import Mathlib.Logic.Relation

namespace Systems

/-! ## Raw networks and tuples -/

/-- Network data before the endpoint and irreflexivity laws are imposed. -/
structure PreNetwork (α : Type*) (κ : Type*) where
  nodes : Set α
  edges : Set (FlowEdge α κ)

/-- The two laws that turn raw network data into a `FlowNetwork`. -/
def PreNetwork.WellFormed {α κ : Type*} (net : PreNetwork α κ) : Prop :=
  (∀ e ∈ net.edges, e.source ∈ net.nodes ∧ e.target ∈ net.nodes) ∧
    ∀ e ∈ net.edges, e.source ≠ e.target

/-- Forget the laws carried by a flow network. -/
def FlowNetwork.toPre {α κ : Type*} (net : FlowNetwork α κ) : PreNetwork α κ where
  nodes := net.nodes
  edges := net.edges

/-- Rebuild a flow network from raw data and an explicit certificate. -/
def PreNetwork.toFlowNetwork {α κ : Type*} (net : PreNetwork α κ)
    (h : net.WellFormed) : FlowNetwork α κ where
  nodes := net.nodes
  edges := net.edges
  edges_on := h.1
  no_self_loops := h.2

theorem FlowNetwork.wellFormed_toPre {α κ : Type*} (net : FlowNetwork α κ) :
    net.toPre.WellFormed :=
  ⟨net.edges_on, net.no_self_loops⟩

theorem PreNetwork.toPre_toFlowNetwork {α κ : Type*} (net : PreNetwork α κ)
    (h : net.WellFormed) : (net.toFlowNetwork h).toPre = net :=
  rfl

theorem FlowNetwork.toFlowNetwork_toPre {α κ : Type*} (net : FlowNetwork α κ) :
    net.toPre.toFlowNetwork net.wellFormed_toPre = net := by
  cases net
  rfl

/-- The Mobus tuple as raw data, with every coherence law removed. -/
structure PreTuple (α : Type*) (κ : Type*) (μ : Type*)
    (π : Type*) (τ : Type*) (η : Type*) (δ : Type*) where
  components : Set α
  internalNetwork : PreNetwork α κ
  environment : MobusEnvironment α μ
  externalFlows : PreNetwork α κ
  boundary : MobusBoundary α π
  transforms : τ
  history : η
  timeScale : δ

/-- The two network laws and six coherence constraints of `MobusSystem`,
stated over raw tuple data. -/
def PreTuple.WellFormed {α κ μ π τ η δ : Type*}
    (sys : PreTuple α κ μ π τ η δ) : Prop :=
  sys.internalNetwork.WellFormed ∧
  sys.externalFlows.WellFormed ∧
  sys.internalNetwork.nodes = sys.components ∧
  sys.components ∩ sys.environment.objects = ∅ ∧
  sys.boundary.interfaces ⊆ sys.components ∧
  (∀ e ∈ sys.externalFlows.edges,
    (e.source ∈ sys.environment.objects ∧ e.target ∈ sys.boundary.interfaces) ∨
    (e.source ∈ sys.boundary.interfaces ∧ e.target ∈ sys.environment.objects)) ∧
  sys.externalFlows.nodes ⊆ sys.environment.objects ∪ sys.boundary.interfaces ∧
  InterfacesCarryEdges sys.externalFlows.edges sys.boundary.interfaces

/-- Forget the laws carried by a well-formed Mobus tuple. -/
def MobusSystem.toPre {α κ μ π τ η δ : Type*}
    (sys : MobusSystem α κ μ π τ η δ) : PreTuple α κ μ π τ η δ where
  components := sys.components
  internalNetwork := sys.internalNetwork.toPre
  environment := sys.environment
  externalFlows := sys.externalFlows.toPre
  boundary := sys.boundary
  transforms := sys.transforms
  history := sys.history
  timeScale := sys.timeScale

/-- Existing `MobusSystem` data satisfies exactly the reified predicate. -/
theorem MobusSystem.wellFormed_toPre {α κ μ π τ η δ : Type*}
    (sys : MobusSystem α κ μ π τ η δ) : sys.toPre.WellFormed :=
  ⟨sys.internalNetwork.wellFormed_toPre,
   sys.externalFlows.wellFormed_toPre,
   sys.network_components,
   sys.disjoint,
   sys.interfaces_sub,
   sys.bipartite,
   sys.externalFlows_nodes,
   sys.interfaces_carry_flow⟩

/-- Build the law-carrying tuple from raw data and its certificate. -/
def PreTuple.toMobus {α κ μ π τ η δ : Type*}
    (sys : PreTuple α κ μ π τ η δ) (h : sys.WellFormed) :
    MobusSystem α κ μ π τ η δ where
  components := sys.components
  internalNetwork := sys.internalNetwork.toFlowNetwork h.1
  environment := sys.environment
  externalFlows := sys.externalFlows.toFlowNetwork h.2.1
  boundary := sys.boundary
  transforms := sys.transforms
  history := sys.history
  timeScale := sys.timeScale
  network_components := h.2.2.1
  disjoint := h.2.2.2.1
  interfaces_sub := h.2.2.2.2.1
  bipartite := h.2.2.2.2.2.1
  externalFlows_nodes := h.2.2.2.2.2.2.1
  interfaces_carry_flow := h.2.2.2.2.2.2.2

/-- Reifying and rebuilding raw data changes none of that data. -/
theorem PreTuple.toPre_toMobus {α κ μ π τ η δ : Type*}
    (sys : PreTuple α κ μ π τ η δ) (h : sys.WellFormed) :
    (sys.toMobus h).toPre = sys :=
  rfl

/-- Forgetting and rebuilding a `MobusSystem` is the identity. -/
theorem MobusSystem.toMobus_toPre {α κ μ π τ η δ : Type*}
    (sys : MobusSystem α κ μ π τ η δ) :
    sys.toPre.toMobus sys.wellFormed_toPre = sys := by
  cases sys
  rfl

/-! ## Lawful life-cycle steps -/

/-- An admissible one-step change. Both regimes act on raw tuples, while the
target certificate states the invariant transported by the step. -/
inductive LifecycleStep {α κ μ π τ η δ : Type*} :
    PreTuple α κ μ π τ η δ → PreTuple α κ μ π τ η δ → Prop
  | grow {before after}
      (wellFormed : after.WellFormed)
      (components : before.components ⊆ after.components) :
      LifecycleStep before after
  | decline {before after}
      (wellFormed : after.WellFormed)
      (components : after.components ⊆ before.components) :
      LifecycleStep before after

/-- Every admissible successor is well-formed. This is non-vacuous because
the successor is raw `PreTuple` data, not a law-carrying `MobusSystem`. -/
theorem wellFormed_of_lifecycleStep {α κ μ π τ η δ : Type*}
    {before after : PreTuple α κ μ π τ η δ}
    (h : LifecycleStep before after) : after.WellFormed := by
  cases h with
  | grow wellFormed _ => exact wellFormed
  | decline wellFormed _ => exact wellFormed

/-- The closure theorem: lawful trajectories of any finite length preserve
the reified well-formedness invariant. -/
theorem wellFormed_of_reaches {α κ μ π τ η δ : Type*}
    {start finish : PreTuple α κ μ π τ η δ}
    (hstart : start.WellFormed)
    (hreaches : Relation.ReflTransGen LifecycleStep start finish) :
    finish.WellFormed := by
  induction hreaches with
  | refl => exact hstart
  | tail _ step _ => exact wellFormed_of_lifecycleStep step

/-! ## The additive regime cannot express decline -/

/-- A transition regime is additive when every step retains all components. -/
def ComponentsAdditive {α κ μ π τ η δ : Type*}
    (r : PreTuple α κ μ π τ η δ → PreTuple α κ μ π τ η δ → Prop) : Prop :=
  ∀ ⦃before after⦄, r before after → before.components ⊆ after.components

/-- Growth-only transitions, separated from the two-regime life cycle. -/
inductive GrowthStep {α κ μ π τ η δ : Type*} :
    PreTuple α κ μ π τ η δ → PreTuple α κ μ π τ η δ → Prop
  | step {before after}
      (wellFormed : after.WellFormed)
      (components : before.components ⊆ after.components) :
      GrowthStep before after

theorem growthStep_additive {α κ μ π τ η δ : Type*} :
    ComponentsAdditive
      (GrowthStep :
        PreTuple α κ μ π τ η δ → PreTuple α κ μ π τ η δ → Prop) := by
  intro before after h
  cases h with
  | step _ components => exact components

/-- Component inclusion is monotone along every finite additive trajectory. -/
theorem additive_components_monotone {α κ μ π τ η δ : Type*}
    {r : PreTuple α κ μ π τ η δ → PreTuple α κ μ π τ η δ → Prop}
    (hadd : ComponentsAdditive r) {start finish}
    (hreaches : Relation.ReflTransGen r start finish) :
    start.components ⊆ finish.components := by
  induction hreaches with
  | refl => exact fun _ h => h
  | tail _ step ih => exact Set.Subset.trans ih (hadd step)

/-- Therefore no additive trajectory can drop a component. -/
theorem not_mem_of_additive_reaches {α κ μ π τ η δ : Type*}
    {r : PreTuple α κ μ π τ η δ → PreTuple α κ μ π τ η δ → Prop}
    (hadd : ComponentsAdditive r) {start finish}
    (hreaches : Relation.ReflTransGen r start finish)
    {component : α} (hstart : component ∈ start.components) :
    component ∈ finish.components :=
  additive_components_monotone hadd hreaches hstart

end Systems
