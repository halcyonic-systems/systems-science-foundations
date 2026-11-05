/-
  Systems/Klir/RosenTriple.lean
  Rosen 1978, §5.8: the system as a triple (S, O, 𝒟)

  Source: Rosen, Fundamentals of Measurement and Representation of Natural
  Systems (Elsevier North-Holland, 1978), §5.8, book p. 128; atlas entry
  rosen-1978-system-triple.

  "a system can be regarded as a triple: a set of states S, a set of
  observables O defined on those states and a family 𝒟 of dynamics imposed
  on the system."

  The atlas rules this a SECOND entry, not a restatement of Definition
  2.9.1's pair (S, F) (entry rosen-1978-formal-system, `RosenShape`,
  `RosenSystem`): the triple adds a coordinate the pair cannot carry, the
  dynamics. The two sit on either side of the static/dynamic seam, and
  Rosen's categorical apparatus (Def 2.9.3, morphisms) is built on the pair
  alone; nothing in the text says what a map of dynamics is. So this file
  adds the triple at the data level beside `RosenSystem` and gives the
  forgetful map back to the pair; it does not retag `RosenShape`.
-/

import Systems.Klir.ViewGeneration
import Systems.Tools.Atlas

namespace Systems

/-- Rosen's system as a triple (1978, §5.8, p. 128): states S, observables O
    "defined on those states", and a family 𝒟 of dynamics "imposed on the
    system".

    Shaped as `RosenSystem` is, so the pair is the triple with 𝒟 forgotten:
    `states` is a subset of a carrier `α`, `observables` the real-valued maps
    with `defined_on` reading "defined on those states" as in the pair, and
    `dynamics` a set of self-maps of the carrier with `imposed_on` reading
    "imposed on the system": a dynamic sends states to states. Rosen's
    hedge "can be regarded as" is the author's and is not formalised; the
    author's own name for the elements of S, "states", is kept. -/
@[atlas "rosen-1978-system-triple"]
structure RosenTriple (α : Type*) where
  /-- S: the set of states. -/
  states : Set α
  /-- O: the set of real-valued observables. -/
  observables : Set (α → ℝ)
  /-- "defined on those states": an observable carries no value off S,
      exactly as `RosenSystem.defined_on`. -/
  defined_on : ∀ f ∈ observables, ∀ x, x ∉ states → f x = 0
  /-- 𝒟: the family of dynamics, as self-maps of the carrier. -/
  dynamics : Set (α → α)
  /-- "imposed on the system": a dynamic sends a state to a state. -/
  imposed_on : ∀ d ∈ dynamics, ∀ x ∈ states, d x ∈ states

/-- The forgetful map from the triple to the pair (S, F) of Definition 2.9.1:
    the states and observables are kept with their `defined_on` proof, the
    dynamics are dropped. This is the one direction the text supports; the
    pair has no slot for 𝒟. -/
def RosenTriple.toRosenSystem {α : Type*} (T : RosenTriple α) : RosenSystem α where
  states := T.states
  observables := T.observables
  defined_on := T.defined_on

/-- The pair underlying a triple keeps its states exactly. -/
theorem RosenTriple.toRosenSystem_states {α : Type*} (T : RosenTriple α) :
    T.toRosenSystem.states = T.states :=
  rfl

/-- The pair underlying a triple keeps its observables exactly. -/
theorem RosenTriple.toRosenSystem_observables {α : Type*} (T : RosenTriple α) :
    T.toRosenSystem.observables = T.observables :=
  rfl

/-- A pair becomes a triple with no dynamics: the empty family. Shows the
    triple is a strict extension in data, not a re-presentation. -/
def RosenSystem.toTriple {α : Type*} (V : RosenSystem α) : RosenTriple α where
  states := V.states
  observables := V.observables
  defined_on := V.defined_on
  dynamics := ∅
  imposed_on := fun _ hd => absurd hd (Set.notMem_empty _)

/-- Forgetting the (empty) dynamics of a lifted pair gives the pair back. -/
theorem RosenSystem.toTriple_toRosenSystem {α : Type*} (V : RosenSystem α) :
    V.toTriple.toRosenSystem = V :=
  rfl

end Systems
