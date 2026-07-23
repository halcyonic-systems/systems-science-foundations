/-
  Systems/Mobus/Bridge.lean
  The Mobus→Bunge bridge: every 8-tuple induces a CES triple

  SHOWCASE THEOREM #1: toBunge is a well-defined map from MobusSystem to
  ConcreteSystem, with formally characterized information loss.

  The bridge maps:
    components       → composition        (exact)
    environment.objects → environment      (milieu M lost)
    totalRelation    → structure'          (capacity κ lost)

  Six fields of the 8-tuple have no Bunge counterpart and are projected
  away: milieu M, boundary properties π, transforms T, history H, time
  scale Δt, and capacity labels κ on flow edges.

  Bunge (1979, philosophical ontology) and Mobus (2022, systems science)
  both descend from Klir's S = (T, R) (1969/2001) but developed their
  elaborations independently — neither references the other. The bridge
  is one edge of a commuting triangle (see Systems/Klir/KlirSystem.lean):
  Mobus → Bunge → Klir = Mobus → Klir, proved by `rfl`. The `rfl` fields
  (composition/components and structure/totalRelation) trace to both
  authors inheriting T = Set α and R = Set (α × α) from Klir without
  changing the mathematical type. The six information loss categories
  mark where Mobus elaborated Klir's framework in directions Bunge's
  philosophical aims did not require.

  SHOWCASE THEOREM #6: The bridge preserves subsystem ordering. If
  sys₁ is a Mobus subsystem of sys₂, then toBunge sys₁ is a Bunge
  subsystem of toBunge sys₂. The proof is ⟨hcomp, henv, hstr⟩ — the
  three-component partial order transfers by direct field mapping.
-/

import Systems.Mobus.Tuple
import Systems.Core.System

namespace Systems

/-! ## Flow-Action Consistency -/

/-- Flow edges induce action: if there is a flow from a to b in the
    internal network, then a acts on b in Bunge's sense.

    This connects Mobus's graph-theoretic representation (flow edges)
    to Bunge's relation-theoretic one (ActsOn). The consistency
    assumption is necessary because ActsOn is abstract (Prop-valued)
    while FlowNetwork is concrete (edge-set-valued). -/
def FlowInducesAction {α : Type*} {κ : Type*} [ActsOn α]
    (net : FlowNetwork α κ) : Prop :=
  ∀ e ∈ net.edges, e.source ▷ e.target

/-! ## The Bridge Map -/

/-- SHOWCASE THEOREM #1: Every well-formed Mobus 8-tuple induces a
    Bunge CES triple.

    The map:
      composition  := components           (exact)
      environment  := environment.objects   (milieu discarded)
      structure'   := totalRelation         (capacity discarded)

    Requires:
    - [ActsOn α]: Bunge's action relation in scope
    - FlowInducesAction: flow edges → action (connects the two frameworks)
    - At least one internal edge (for Bunge's bondage_nonempty)

    Information projected away (no Bunge counterpart):
      milieu M, boundary properties π, transforms τ,
      history η, time scale δ, capacity labels κ -/
def MobusSystem.toBunge {α κ μ π τ η δ : Type*} [ActsOn α]
    (sys : MobusSystem α κ μ π τ η δ)
    (hflow : FlowInducesAction sys.internalNetwork)
    (hedge : sys.internalNetwork.edges.Nonempty) :
    ConcreteSystem α where
  composition := sys.components
  environment := sys.environment.objects
  structure' := sys.totalRelation
  disjoint := sys.disjoint
  structure_on := sys.totalRelation_on
  bondage_nonempty := by
    obtain ⟨e, he⟩ := hedge
    have hon := sys.internalNetwork.edges_on e he
    rw [sys.network_components] at hon
    exact ⟨e.source, hon.1, e.target, hon.2,
           sys.internalNetwork.no_self_loops e he,
           Or.inl (hflow e he)⟩

/-! ## Field Characterization -/

/-- The bridge maps components to composition exactly. -/
theorem MobusSystem.toBunge_composition {α κ μ π τ η δ : Type*} [ActsOn α]
    (sys : MobusSystem α κ μ π τ η δ) (hf hg) :
    (sys.toBunge hf hg).composition = sys.components :=
  rfl

/-- The bridge maps environment objects to environment (milieu lost). -/
theorem MobusSystem.toBunge_environment {α κ μ π τ η δ : Type*} [ActsOn α]
    (sys : MobusSystem α κ μ π τ η δ) (hf hg) :
    (sys.toBunge hf hg).environment = sys.environment.objects :=
  rfl

/-- The bridge maps totalRelation to structure (capacity lost). -/
theorem MobusSystem.toBunge_structure {α κ μ π τ η δ : Type*} [ActsOn α]
    (sys : MobusSystem α κ μ π τ η δ) (hf hg) :
    (sys.toBunge hf hg).structure' = sys.totalRelation :=
  rfl

/-! ## Subsystem Preservation -/

/-- Mobus subsystem relation: the Mobus counterpart of Bunge's Def 1.6.
    A Mobus system is a subsystem of another if it has fewer components,
    more environment objects, and fewer relations — the same asymmetry
    as Bunge's (a subsystem sees the rest as part of its environment). -/
def MobusSubsystem {α κ μ π τ η δ : Type*}
    (sys₁ sys₂ : MobusSystem α κ μ π τ η δ) : Prop :=
  sys₁.components ⊆ sys₂.components ∧
  sys₂.environment.objects ⊆ sys₁.environment.objects ∧
  sys₁.totalRelation ⊆ sys₂.totalRelation

/-- SHOWCASE THEOREM #6: The bridge preserves subsystem ordering.
    If sys₁ is a Mobus subsystem of sys₂, then their Bunge projections
    stand in Bunge's subsystem relation.

    The proof is the triple ⟨hcomp, henv, hstr⟩ — the three subset
    conditions transfer directly because toBunge maps each field exactly.
    This is another "clean composition" result: the right representation
    makes the theorem trivial. -/
theorem toBunge_preserves_subsystem {α κ μ π τ η δ : Type*} [ActsOn α]
    (sys₁ sys₂ : MobusSystem α κ μ π τ η δ)
    (hf₁ : FlowInducesAction sys₁.internalNetwork)
    (hg₁ : sys₁.internalNetwork.edges.Nonempty)
    (hf₂ : FlowInducesAction sys₂.internalNetwork)
    (hg₂ : sys₂.internalNetwork.edges.Nonempty)
    (hsub : MobusSubsystem sys₁ sys₂) :
    Subsystem (sys₁.toBunge hf₁ hg₁) (sys₂.toBunge hf₂ hg₂) :=
  ⟨hsub.1, hsub.2.1, hsub.2.2⟩

/-! ## Information Loss Characterization

The bridge is a *projection*: it maps a richer structure (8-tuple) to a
simpler one (CES triple). The following six categories of information
have no Bunge counterpart and are discarded:

1. **Milieu M** (Environment.lean) — ambient variables without discrete
   sources. Bunge's E is a set of things; Mobus's E = ⟨O, M⟩ splits
   discrete objects from ambient conditions.
   Loss witnessed by: `toBunge_environment` = `environment.objects` (not `environment`)

2. **Capacity κ** (FlowNetwork.lean) — quantitative flow labels on edges.
   Bunge's S is a set of pairs; Mobus's N and G carry capacity functions.
   Loss witnessed by: `totalRelation` uses `FlowNetwork.toRelation` which
   discards capacity.

3. **Boundary properties π** (Boundary.lean) — Mobus admits the exact form
   is "still an object of research." Bunge has no boundary concept.

4. **Transforms τ** — domain-specific processing functions. Bunge's
   framework is structural (what's connected), not functional (what
   things do to their inputs).
   This is the coordinate that carries Bunge's *mechanism* M(σ). The bridge
   still discards it, so `toBunge` delivers CES (not CESM) — no M slot here.
   M is approximated by `MechanismSpec` (Systems/Dynamics/Mechanism.lean): the
   declared dynamics descriptor + typed transition, i.e. the coalgebra GENERATOR.
   Full M(σ) requires unfolding that generator to the behavior set H (M ⊆ S^ω,
   Bunge's "set of characteristic processes"), which is not yet a first-class Lean
   type. Retitling to CESM is deferred to #97 Increment 2 (type H + verify the
   unfolding + discharge the emptiness constraint on H).

5. **History η** — stored knowledge / memory. Bunge addresses history
   in §2.2 (state functions over time) but not as a system component.

6. **Time scale δ** — Δt, the temporal resolution. Bunge's definitions
   are time-indexed but the time structure itself is not formalized
   (see retrospective §2a).

These losses are not deficiencies — they are the formal content of the
divergence between two independently developed frameworks. Bunge
(philosophical ontology, 1979) and Mobus (systems science, 2022) arrived
at compatible structures from different traditions without mutual
reference. The projection is not injective: multiple Mobus systems
(differing in milieu, capacity, transforms, etc.) map to the same Bunge
CES triple. The six loss categories mark the precise points where Mobus's
engineering orientation led to distinctions that Bunge's philosophical
orientation did not require.

This is **independent convergence with formally characterized divergence**.
The `rfl` proofs on the three preserved fields (composition, environment
objects, total relation) are not trivially expected — they are empirical
findings that two researchers using different notation, terminology, and
motivating examples happened to decompose a system in the same way.
-/

/-- Two Mobus systems that agree on components, environment objects,
    and total relation project to Bunge systems with identical CES
    triples — regardless of differences in milieu, boundary, transforms,
    history, or time scale.

    This is the formal statement of information loss: the bridge
    is not injective. -/
theorem toBunge_eq_of_structural_eq {α κ μ π τ η δ : Type*} [ActsOn α]
    (sys₁ sys₂ : MobusSystem α κ μ π τ η δ)
    (hf₁ : FlowInducesAction sys₁.internalNetwork)
    (hg₁ : sys₁.internalNetwork.edges.Nonempty)
    (hf₂ : FlowInducesAction sys₂.internalNetwork)
    (hg₂ : sys₂.internalNetwork.edges.Nonempty)
    (hc : sys₁.components = sys₂.components)
    (he : sys₁.environment.objects = sys₂.environment.objects)
    (hs : sys₁.totalRelation = sys₂.totalRelation) :
    (sys₁.toBunge hf₁ hg₁).composition = (sys₂.toBunge hf₂ hg₂).composition ∧
    (sys₁.toBunge hf₁ hg₁).environment = (sys₂.toBunge hf₂ hg₂).environment ∧
    (sys₁.toBunge hf₁ hg₁).structure' = (sys₂.toBunge hf₂ hg₂).structure' :=
  ⟨hc, he, hs⟩

end Systems
