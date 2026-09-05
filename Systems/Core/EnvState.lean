/-
  Systems/Core/EnvState.lean
  The joint state with an ENVIRONMENT coordinate (decision A, 2026-09-04).

  `JointState` (JointState.lean) takes its product over `composition` only, so the
  things in `environment` carry no coordinate. NonDegenerate.lean's header records the
  cost: an environment that changes "cannot ride on it without changing that
  definition", and `EvolvesByEnv` had to be stated on the bare product `S × E` of
  `CoupledDynamicSystem` instead. This file adds the coordinate without touching
  `JointState`: a carrier `StateCarrierE` extends `StateCarrier` with a state set
  `QE` for environment things, and `JointStateE` is the system's joint state paired
  with one reading per environment thing.

  SOURCES.
  - Mobus's E slot: `MobusSystem.environment : MobusEnvironment α μ`
    (Systems/Mobus/Tuple.lean, "E: the environment ⟨O, M⟩. O = discrete objects,
    M = opaque milieu"). The objects `O` are the things this coordinate is indexed
    by; the milieu `M` is what `QE` reads off each of them.
  - George Mobus on the history object H (mobus-lifecycle-paper/source-materials/
    h-object-mobus-notes.md:11): "all the relevant state variables for the system of
    interest ... are aggregated into a single image structure. For modeling
    CAS/CAESs, the image would include all the relevant environment variables as
    well." And :25: "the history should not only be of the images of the system
    variables but include certain environment variables as well." The image he
    describes is a `JointStateE`, not a `JointState`.
  - Mobus & Kalton 2015 §10.2.1.4: fitness "has no meaning without considering a
    system's environment" — the reason Evolution.lean's `EvolutionE` needs an
    environment coordinate to index its fitness family by.

  `JointStateE c` is definitionally a product `JointState c.toStateCarrier × Env c`,
  so `EvolutionE (JointState c.toStateCarrier) (EnvState c)` (Evolution.lean) and
  `HomeostatD _ O (EnvState c)` (Governance.lean) apply to it directly: the `S × E`
  of NonDegenerate.lean now has a CES-indexed instance.

  One theorem (`envState_subsingleton_of_closed`); the two projections are definitional.
-/

import Systems.Core.JointState

namespace Systems

universe u v w

variable {α : Type u} [ActsOn α]

/-- A state carrier with a state set for each ENVIRONMENT thing as well as each
    component. `Q` and `K` are inherited from `StateCarrier`; `QE` is the milieu
    reading on each object of Mobus's `E = ⟨O, M⟩` (Tuple.lean). -/
structure StateCarrierE (α : Type u) [ActsOn α] extends StateCarrier.{u, v, w} α where
  /-- Per-environment-thing state set (the `M` read off each `O`). -/
  QE : α → Type v

/-- The environment coordinate alone: one reading per environment thing. -/
def EnvState (c : StateCarrierE.{u, v, w} α) : Type (max u v) :=
  (e : {e // e ∈ c.system.environment}) → c.QE e.1

/-- The joint state WITH environment: the system's joint state (components and
    flows, as in `JointState`) paired with the environment coordinate. This is the
    "image" of h-object-mobus-notes.md:11 that "would include all the relevant
    environment variables as well". -/
def JointStateE (c : StateCarrierE.{u, v, w} α) : Type (max u v w) :=
  JointState c.toStateCarrier × EnvState c

/-- Projection onto the system's own joint state (drop the environment). -/
def JointStateE.sys {c : StateCarrierE.{u, v, w} α} (x : JointStateE c) :
    JointState c.toStateCarrier :=
  x.1

/-- Projection onto the environment coordinate. -/
def JointStateE.env {c : StateCarrierE.{u, v, w} α} (x : JointStateE c) : EnvState c :=
  x.2

/-- A carrier whose environment is empty has a trivial environment coordinate, so
    `JointStateE` carries exactly the information of `JointState`: the old bridge is
    the closed-system case of this one (`System.lean`, `IsClosed`).
    `#print axioms`: Quot.sound. -/
theorem envState_subsingleton_of_closed (c : StateCarrierE.{u, v, w} α)
    (h : c.system.environment = ∅) : Subsingleton (EnvState c) :=
  ⟨fun _ _ => funext fun e => absurd (h ▸ e.2) (Set.notMem_empty e.1)⟩

end Systems
