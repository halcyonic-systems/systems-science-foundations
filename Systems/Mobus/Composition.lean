/-
  Systems/Mobus/Composition.lean
  Bipartite transfer under composition — the 8-tuple testable prediction

  FINDING: 8-tuple composition is unconditional, like CES composition.
  The bipartite constraint on external flows transfers because
  composition only REMOVES external edges (reclassifying them as
  internal when both endpoints become components). It never ADDS edges.

  The key theorem (bipartite_edge_classification): if external flows
  are bipartite between environment A and interfaces B, and B ⊆ C
  (composed components), then every edge NOT fully inside C has
  exactly one endpoint in C and one outside. This guarantees the
  surviving edges remain bipartite.

  Mobus, Systems Science: Theory, Analysis, Modeling, and Design, Ch. 4.
-/

import Systems.Mobus.Tuple
import Systems.Mobus.Interface

namespace Systems

/-! ## Bipartite Transfer Under Composition

  The core argument:
  1. Bipartite: each edge has source ∈ A (env), target ∈ B (interfaces), or reverse
  2. B ⊆ C (interfaces ⊆ components ⊆ composedComp)
  3. If the A-endpoint is also in C → both in C → edge reclassified as internal
  4. If the A-endpoint is NOT in C → edge survives, one in C, one outside
  5. No edge connects two A-elements or two B-elements (bipartite)
  6. Therefore every surviving edge crosses the composed boundary -/

/-- Bipartite edge classification under composition.

    Given: a flow network bipartite between sets A and B, with B ⊆ C.
    Then: every edge that is NOT fully inside C has exactly one endpoint
    in C and one outside C.

    This is the structural content of "bipartite transfers": the
    B-endpoint is always in C (since B ⊆ C). If the A-endpoint is
    also in C, both are inside and the edge is filtered. If not,
    the edge survives with one endpoint in, one out. -/
theorem bipartite_edge_classification {α κ : Type*}
    {net : FlowNetwork α κ}
    {A B C : Set α}
    (hbp : IsBipartiteFlow net A B)
    (hB_sub_C : B ⊆ C) :
    ∀ e ∈ net.edges, ¬(e.source ∈ C ∧ e.target ∈ C) →
      (e.source ∉ C ∧ e.target ∈ C) ∨ (e.source ∈ C ∧ e.target ∉ C) := by
  intro e he hne
  rcases hbp e he with ⟨hs_A, ht_B⟩ | ⟨hs_B, ht_A⟩
  · have ht_C := hB_sub_C ht_B
    have hs_nC : e.source ∉ C := fun hc => hne ⟨hc, ht_C⟩
    exact Or.inl ⟨hs_nC, ht_C⟩
  · have hs_C := hB_sub_C hs_B
    have ht_nC : e.target ∉ C := fun hc => hne ⟨hs_C, hc⟩
    exact Or.inr ⟨hs_C, ht_nC⟩

/-- In a MobusSystem, external edges surviving composition have
    exactly one endpoint in the composed components.

    `sys.components ⊆ composedComp` (the system is part of a
    composition). Any external edge not fully inside composedComp
    has one endpoint in composedComp (an interface) and one outside
    (in the composed environment). -/
theorem MobusSystem.external_edges_survive_bipartite
    {α κ μ π τ η δ : Type*}
    (sys : MobusSystem α κ μ π τ η δ)
    (composedComp : Set α)
    (h_sub : sys.components ⊆ composedComp) :
    ∀ e ∈ sys.externalFlows.edges,
      ¬(e.source ∈ composedComp ∧ e.target ∈ composedComp) →
      (e.source ∉ composedComp ∧ e.target ∈ composedComp) ∨
      (e.source ∈ composedComp ∧ e.target ∉ composedComp) :=
  bipartite_edge_classification sys.bipartite (sys.interfaces_sub.trans h_sub)

end Systems
