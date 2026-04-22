/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic
import Systems.Category.ShapeWymore
import Systems.Category.ShapeMobus

/-!
# Comparison Functor: I_Wymore → I_Mobus

The comparison functor embeds Wymore's FSD shape into Mobus's 8-tuple shape.

## The Arrow Direction Problem (Again)

Wymore's arrows radiate OUTWARD from `state` (functional direction: state produces
output, consumes input, is indexed by time). Mobus's arrows converge INWARD toward
`components` (dependency direction: network/boundary/environment all depend on
components).

The only Mobus position with 2+ outgoing arrows is `externalFlows` (G), which has
arrows to `environment` and `boundary`. This is the best candidate for Wymore's `state`.

## Mapping

| Wymore | Mobus | Interpretation |
|--------|-------|---------------|
| state | externalFlows | the system's operational behavior lives at the I/O interface |
| output | environment | what the system produces flows to the environment |
| input | boundary | what the system consumes enters through the boundary |
| time | components | temporal structure is grounded in component structure |

## Key Finding: The Length-2 Path

Two of three arrows map cleanly to generating arrows:
- `readout` → `external_on_env` (G → E): output flows to environment ✓
- `nextState` → `external_on_boundary` (G → B): input enters through boundary ✓

But `stateOnTime` requires a LENGTH-2 composite path:
- `stateOnTime` → G → B → C (external_on_boundary ≫ interfaces_in_components)

This composite reveals that Mobus MEDIATES the time-state relationship through
the boundary: temporal grounding passes through interface structure before reaching
components. Wymore treats time as directly indexing state; Mobus requires time to
be grounded through the boundary layer. The length-2 path IS the structural content
of their disagreement about where time enters the system.
-/

open CategoryTheory

/-- Object-level comparison: Wymore positions projected into Mobus's 8-tuple. -/
def wymoreToMobusObj : WymorePosition → MobusPosition
  | .state  => .externalFlows
  | .output => .environment
  | .input  => .boundary
  | .time   => .components

/-- The comparison as a prefunctor into the Mobus path category.

Two arrows map to length-1 paths (generating arrows); one maps to a length-2
composite path through boundary → components. -/
def wymoreToMobusPre : Prefunctor WymorePosition (Paths MobusPosition) where
  obj := wymoreToMobusObj
  map := fun
    | .readout     => Quiver.Hom.toPath MobusArrow.external_on_env
    | .nextState   => Quiver.Hom.toPath MobusArrow.external_on_boundary
    | .stateOnTime =>
        (Quiver.Hom.toPath MobusArrow.external_on_boundary).cons
          MobusArrow.interfaces_in_components

/-- The comparison functor from I_Wymore to I_Mobus. -/
def wymoreToMobusFunctor : Paths WymorePosition ⥤ Paths MobusPosition :=
  Paths.lift wymoreToMobusPre

-- § Object characterization

theorem wymoreToMobusFunctor_obj (p : WymorePosition) :
    wymoreToMobusFunctor.obj p = wymoreToMobusObj p := rfl

-- § Arrow lengths reveal structural mediation

/-- Readout maps to a length-1 path: direct correspondence. -/
theorem wymore_readout_length :
    (wymoreToMobusPre.map WymoreArrow.readout).length = 1 := rfl

/-- NextState maps to a length-1 path: direct correspondence. -/
theorem wymore_nextState_length :
    (wymoreToMobusPre.map WymoreArrow.nextState).length = 1 := rfl

/-- StateOnTime maps to a length-2 path: Mobus mediates time through boundary.
This is the structural content of their disagreement — Wymore allows state to be
directly time-indexed, while Mobus requires temporal grounding to pass through
the interface/boundary layer before reaching components. -/
theorem wymore_stateOnTime_length :
    (wymoreToMobusPre.map WymoreArrow.stateOnTime).length = 2 := rfl

/-- The length asymmetry: stateOnTime requires strictly more structure in Mobus
than the other two arrows. -/
theorem wymore_time_mediated :
    (wymoreToMobusPre.map WymoreArrow.stateOnTime).length >
    (wymoreToMobusPre.map WymoreArrow.readout).length := by
  native_decide

-- § Object-injectivity: all four Wymore positions land on distinct Mobus positions

/-- The comparison is injective on objects — no Wymore positions collapse.
This is stronger than the Mobus→Bunge or Mobus→Myers comparisons, where
multiple positions collapse. Wymore's 4-position structure fits cleanly
into Mobus's 8-position framework with room to spare. -/
theorem wymoreToMobusObj_injective : Function.Injective wymoreToMobusObj := by
  intro a b h; cases a <;> cases b <;> simp_all [wymoreToMobusObj]
