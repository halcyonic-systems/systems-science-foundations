/-
  Systems/Mobus/Boundary.lean
  System boundary: properties and interfaces

  Formalizes Mobus Eq. 4.6:
    B_{i,l} = ⟨P_{i,l}, I_{i,l}⟩
  where P is the set of boundary properties and I is the set of
  interface components — components that transport flows across the
  boundary between system and environment.

  Mobus: "The exact form of P is still an object of research."
  We keep boundary properties parametric (type π).

  SHOWCASE THEOREM #3 (boundary completeness): Every external flow
  passes through an interface. Non-interface components do not
  participate in external flows — the boundary mediates all
  system-environment interaction.
-/

import Systems.Mobus.FlowNetwork

namespace Systems

/-! ## Mobus Boundary -/

/-- The boundary of a Mobus system: properties and interfaces.
    Mobus Eq. 4.6: B_{i,l} = ⟨P_{i,l}, I_{i,l}⟩

    - P: boundary properties (parametric — Mobus defers their exact form)
    - I: interface components that mediate flows across the boundary

    Parametrized by:
    - α: node type (interfaces are components, sharing the type)
    - π: boundary property type (domain-supplied, opaque) -/
structure MobusBoundary (α : Type*) (π : Type*) where
  /-- Boundary properties.
      Mobus: "The exact form of P is still an object of research." -/
  properties : π
  /-- Interface components: the subset of components that transport
      flows across the boundary. Every external flow edge has its
      component-side endpoint in this set. -/
  interfaces : Set α

/-! ## Boundary Completeness -/

/-- Boundary completeness: every external flow edge passes through an
    interface. If an edge endpoint is not an environmental object, it
    must be an interface component.

    This is the formal statement of the boundary principle: non-interface
    components are "shielded" from the environment by the boundary. -/
def BoundaryComplete {α : Type*} {κ : Type*} {π : Type*}
    (boundary : MobusBoundary α π)
    (externalFlows : FlowNetwork α κ)
    (envObjects : Set α) : Prop :=
  ∀ e ∈ externalFlows.edges,
    (e.source ∉ envObjects → e.source ∈ boundary.interfaces) ∧
    (e.target ∉ envObjects → e.target ∈ boundary.interfaces)

/-- SHOWCASE THEOREM #3: If the boundary is complete, then every external
    flow edge has both endpoints in the union of interfaces and environment
    objects. No flow reaches a non-interface component directly.

    This is what systems theorists mean by "the boundary mediates all
    interaction with the environment." -/
theorem boundary_complete_endpoints {α : Type*} {κ : Type*} {π : Type*}
    (boundary : MobusBoundary α π)
    (flows : FlowNetwork α κ)
    (envObjects : Set α)
    (hbc : BoundaryComplete boundary flows envObjects) :
    ∀ e ∈ flows.edges,
      e.source ∈ boundary.interfaces ∪ envObjects ∧
      e.target ∈ boundary.interfaces ∪ envObjects := by
  intro e he
  have ⟨hs, ht⟩ := hbc e he
  constructor
  · by_cases h : e.source ∈ envObjects
    · exact Set.mem_union_right _ h
    · exact Set.mem_union_left _ (hs h)
  · by_cases h : e.target ∈ envObjects
    · exact Set.mem_union_right _ h
    · exact Set.mem_union_left _ (ht h)

/-- Contrapositive of boundary completeness: a component that is neither
    an interface nor an environmental object does not appear as an
    endpoint in any external flow edge.

    This is the "shielding" property — internal (non-interface) components
    are invisible to the environment. -/
theorem non_interface_shielded {α : Type*} {κ : Type*} {π : Type*}
    (boundary : MobusBoundary α π)
    (flows : FlowNetwork α κ)
    (envObjects : Set α)
    (hbc : BoundaryComplete boundary flows envObjects)
    (a : α) (hni : a ∉ boundary.interfaces) (hne : a ∉ envObjects) :
    ∀ e ∈ flows.edges, e.source ≠ a ∧ e.target ≠ a := by
  intro e he
  have ⟨hs, ht⟩ := hbc e he
  constructor
  · intro ha
    have : e.source ∉ envObjects := by rw [ha]; exact hne
    have := hs this
    rw [ha] at this
    exact absurd this hni
  · intro ha
    have : e.target ∉ envObjects := by rw [ha]; exact hne
    have := ht this
    rw [ha] at this
    exact absurd this hni

end Systems
