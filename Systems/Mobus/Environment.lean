/-
  Systems/Mobus/Environment.lean
  Mobus environment: discrete objects and opaque milieu

  Formalizes the revised E element from the Mobus 8-tuple (book-revisions):
    E = ⟨O, M⟩
  where O is the set of discrete environmental objects (sources and sinks)
  and M is the milieu — non-point-source variables that surround the system.

  Mobus: "M is the set of variables that are part of the environment but do
  not have a discrete (point) source. They surround or 'bathe' the system in
  conditions that impact or influence the state of the system."

  DESIGN: Milieu is parametric (type μ). Mobus gives examples
  (Temp, Humidity, Salinity, pH, Pressure) but no formal structure —
  the milieu is domain-supplied. Objects O share the node type α with
  components, since environmental objects participate in flow networks
  (the G edges connect o_i ∈ O to c_j ∈ C).

  Bunge's environment E_A(σ,t) is a flat set of things. The Mobus→Bunge
  projection maps O to Bunge's E and discards M entirely — milieu has
  no Bunge counterpart. This is one of two systematic information losses
  in the bridge (the other being flow capacity in N; see FlowNetwork.lean).
-/

import Mathlib.Data.Set.Basic

namespace Systems

/-! ## Mobus Environment -/

/-- The environment of a Mobus system: discrete objects plus opaque milieu.
    Book-revisions: E = ⟨O, M⟩

    - O: set of discrete environmental objects that interact with the system
      through flow edges (G network). Objects can be sources, sinks, or both.
    - M: the milieu — ambient conditions that influence the system without
      discrete point-source interfaces.

    Parametrized by:
    - α: node type (shared with components — objects appear in flow networks)
    - μ: milieu type (domain-supplied, opaque to the ontology) -/
structure MobusEnvironment (α : Type*) (μ : Type*) where
  /-- Discrete environmental objects: sources and sinks.
      Mobus: O = ⟨o₀, o₁, ..., oₘ⟩ -/
  objects : Set α
  /-- The milieu: ambient variables without discrete point sources.
      Mobus example: M = ⟨Temp, Humidity, Salinity, pH, Pressure⟩ -/
  milieu : μ

/-! ## Projection to Bunge -/

/-- Project a Mobus environment to Bunge's flat environment set.
    Bunge's E_A(σ,t) is a set of things — it corresponds to Mobus's O
    (discrete objects). The milieu M has no Bunge counterpart and is
    discarded by this projection.

    This is one of two systematic information losses in the Mobus→Bunge
    bridge (the other being flow capacity; see FlowNetwork.toRelation). -/
def MobusEnvironment.toBungeEnvironment {α : Type*} {μ : Type*}
    (env : MobusEnvironment α μ) : Set α :=
  env.objects

/-- Two Mobus environments with the same objects project to the same
    Bunge environment, regardless of milieu. -/
theorem MobusEnvironment.toBunge_eq_of_objects_eq {α : Type*} {μ : Type*}
    (env₁ env₂ : MobusEnvironment α μ)
    (h : env₁.objects = env₂.objects) :
    env₁.toBungeEnvironment = env₂.toBungeEnvironment :=
  h

/-! ## Empty and Trivial Environments -/

/-- An environment with no discrete objects and a given milieu.
    The system interacts with ambient conditions but has no discrete
    sources or sinks. -/
def MobusEnvironment.milieuOnly {α : Type*} {μ : Type*}
    (m : μ) : MobusEnvironment α μ where
  objects := ∅
  milieu := m

/-- A milieu-only environment has empty Bunge projection. -/
theorem MobusEnvironment.milieuOnly_bunge_empty {α : Type*} {μ : Type*}
    (m : μ) : (MobusEnvironment.milieuOnly m : MobusEnvironment α μ).toBungeEnvironment = ∅ :=
  rfl

end Systems
