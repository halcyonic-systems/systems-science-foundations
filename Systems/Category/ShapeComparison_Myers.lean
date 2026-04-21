/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic
import Systems.Category.ShapeMobus
import Systems.Category.ShapeMyers

/-!
# Comparison Functor: I_Mobus → I_Myers

The comparison functor projects the Mobus 8-tuple shape onto Myers's minimal
deterministic system (lens) shape.

## The Direction Problem

Mobus's arrows converge INWARD (everything depends on components — C is a sink).
Myers's arrows radiate OUTWARD (State exposes to Out, depends on In — State is a source).

This directional incompatibility means: the comparison cannot simultaneously
preserve both expose and update. The natural mapping sends all structural
constraints to `expose` (Mobus is about what systems REVEAL through decomposition)
while `update` has NO preimage (Mobus encodes no dynamics at the structural level).

## Key Result

The comparison functor maps:
- `components → output` (what the system is made of = what gets observed)
- Everything else → `state` (internal structure IS the opaque state)
- All non-trivial Mobus arrows → `expose` (structural constraints = observation)
- Myers's `update` has NO Mobus preimage

This formally diagnoses: **Mobus captures statics (what is the system?),
Myers captures dynamics (how does the system behave?).** The structural
constraints all relate to observation; none relate to state transitions.
-/

open CategoryTheory

/-- Object-level comparison: Mobus positions projected into Myers's lens schema.

The mapping reflects the statics/dynamics split:
- `components → output`: composition is the OBSERVABLE aspect of a system
- All other positions → `state`: internal structure is opaque state
  from the lens perspective

Note: `environment` maps to `state` (not `input`) because Mobus's environment
participates in structural constraints (disjointness, flow endpoints) that are
all about characterizing the system's observable decomposition, not about
feeding it dynamic input. -/
def myersComparisonObj : MobusPosition → MyersPosition
  | .components       => .output
  | .internalNetwork  => .state
  | .environment      => .state
  | .externalFlows    => .state
  | .boundary         => .state
  | .transforms       => .state
  | .history          => .state
  | .timeScale        => .state

/-- The comparison as a prefunctor into the Myers path category.

Three Mobus arrows (N→C, B→C, E→C) map to `expose` — they all express
"internal structure produces/constrains the observable composition."
Two Mobus arrows (G→E, G→B) map to identity — they relate things within
the `state` abstraction. -/
def myersComparisonPre : Prefunctor MobusPosition (Paths MyersPosition) where
  obj := myersComparisonObj
  map := fun
    | .network_on_components    => Quiver.Hom.toPath MyersArrow.expose
    | .interfaces_in_components => Quiver.Hom.toPath MyersArrow.expose
    | .external_on_env          => Quiver.Path.nil
    | .external_on_boundary     => Quiver.Path.nil
    | .env_disjoint_comp        => Quiver.Hom.toPath MyersArrow.expose

/-- The comparison functor from I_Mobus to I_Myers. -/
def myersComparisonFunctor : Paths MobusPosition ⥤ Paths MyersPosition :=
  Paths.lift myersComparisonPre

-- § Object-level characterization

theorem myersComparisonFunctor_obj (p : MobusPosition) :
    myersComparisonFunctor.obj p = myersComparisonObj p := rfl

-- § Fiber characterization

/-- State absorbs 7 Mobus positions — everything except components. -/
theorem myers_fiber_state (p : MobusPosition) :
    myersComparisonObj p = .state ↔
    p = .internalNetwork ∨ p = .environment ∨ p = .externalFlows ∨
    p = .boundary ∨ p = .transforms ∨ p = .history ∨ p = .timeScale := by
  cases p <;> simp [myersComparisonObj]

/-- Output is a singleton fiber — components are what gets observed. -/
theorem myers_fiber_output (p : MobusPosition) :
    myersComparisonObj p = .output ↔ p = .components := by
  cases p <;> simp [myersComparisonObj]

/-- Input has an empty fiber — no Mobus position maps to Myers's input.
This is the categorical content of "Mobus has no dynamics concept." -/
theorem myers_fiber_input (p : MobusPosition) :
    myersComparisonObj p ≠ .input := by
  cases p <;> simp [myersComparisonObj]

-- § Arrow behavior

/-- Three Mobus arrows map to `expose` — all structural observation. -/
theorem myers_expose_preimages :
    myersComparisonPre.map MobusArrow.network_on_components =
      Quiver.Hom.toPath MyersArrow.expose ∧
    myersComparisonPre.map MobusArrow.interfaces_in_components =
      Quiver.Hom.toPath MyersArrow.expose ∧
    myersComparisonPre.map MobusArrow.env_disjoint_comp =
      Quiver.Hom.toPath MyersArrow.expose :=
  ⟨rfl, rfl, rfl⟩

/-- Two Mobus arrows are annihilated (internal wiring). -/
theorem myers_arrows_annihilated :
    myersComparisonPre.map MobusArrow.external_on_env = Quiver.Path.nil ∧
    myersComparisonPre.map MobusArrow.external_on_boundary = Quiver.Path.nil :=
  ⟨rfl, rfl⟩

-- § The punchline: update has no preimage

/-- Myers's `update` arrow targets `input`, but no Mobus position maps to `input`.
Therefore `update` cannot appear in the image of any Mobus arrow under the comparison.

This is the formal content of "Mobus is structural, Myers is computational":
- Mobus captures what systems ARE (observation/decomposition → expose)
- Myers captures how systems BEHAVE (dynamics/transitions → update)
- The missing `update` is exactly what BERT's transform (T) is supposed to provide
  operationally — but T is isolated in I_Mobus (no generating arrows), so it cannot
  fill this gap at the shape level. -/
theorem myers_update_unreachable :
    ∀ (a b : MobusPosition) (_ : MobusArrow a b),
      myersComparisonObj b ≠ .input := by
  intro a b f
  cases f <;> simp [myersComparisonObj]

-- § Non-injectivity

theorem myersComparisonObj_not_injective : ¬ Function.Injective myersComparisonObj := by
  intro h
  exact absurd (h (show myersComparisonObj .internalNetwork = myersComparisonObj .environment from rfl))
    (by exact MobusPosition.noConfusion)
