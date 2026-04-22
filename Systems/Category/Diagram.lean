/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Types.Basic
import Systems.Category.ShapeBunge
import Systems.Core.System

/-!
# Systems as Diagrams of Shape I_Bunge

A system-as-diagram is a functor `F : I_Bunge → Type`, assigning a type to each
position and a function to each dependency arrow.

## The Gap Between CES Data and CES Diagrams

A `ConcreteSystem` provides three *sets* (C, E, S) with constraints. But the shape
category's arrows demand *functions*:
- `struct_on_comp` requires `F(S) → F(C)`: extract a component from a structural pair
- `struct_on_env` requires `F(S) → F(E)`: extract an environment element from a pair
- `env_acts_on_comp` requires `F(E) → F(C)`: map each environment element to a component

None of these exist as canonical total functions for general concrete systems:
- A structural pair `(a, b) ∈ S` has `a ∈ C ∪ E` — not necessarily in C alone
- The environment-component interaction is a *relation*, not a function

This gap is the mathematical content: the shape category reveals that interpreting
a system as a diagram requires *choosing* projection morphisms. A `BungeDiagram`
bundles these choices with the system data.
-/

open Systems CategoryTheory

universe u

/-- A Bunge diagram is a concrete system equipped with morphism data that allows
it to be interpreted as a functor from the shape category to Type.

The three functions witness the structural dependencies encoded by the shape arrows:
- `proj_comp`: for each structural relation, identify a component it involves
- `proj_env`: for each structural relation, identify an environment element it involves
- `interact`: for each environment element, identify a component it interacts with -/
structure BungeDiagram (α : Type u) [ActsOn α] where
  system : ConcreteSystem α
  proj_comp : ↥system.structure' → ↥system.composition
  proj_env : ↥system.structure' → ↥system.environment
  interact : ↥system.environment → ↥system.composition

/-- The prefunctor from the Bunge quiver into the category of types,
determined by a `BungeDiagram`.

Objects map to subtypes of the carrier; each generating arrow maps to
the corresponding projection function provided by the diagram. -/
def BungeDiagram.pre {α : Type u} [ActsOn α] (d : BungeDiagram α) :
    Prefunctor BungePosition (Type u) where
  obj pos := match pos with
    | .composition => ↥d.system.composition
    | .environment => ↥d.system.environment
    | .structure'  => ↥d.system.structure'
  map {X Y} f := match X, Y, f with
    | .structure', .composition, .struct_on_comp => fun x => d.proj_comp x
    | .structure', .environment, .struct_on_env => fun x => d.proj_env x
    | .environment, .composition, .env_acts_on_comp => fun x => d.interact x

/-- A Bunge diagram gives rise to a functor from I_Bunge to Type via `Paths.lift`.

The universal property of the free category guarantees functoriality: composition of
path-level morphisms is handled by function composition in Type. -/
def BungeDiagram.toFunctor {α : Type u} [ActsOn α] (d : BungeDiagram α) :
    Paths BungePosition ⥤ Type u :=
  Paths.lift d.pre

/-- The functor assigns the composition subtype to the composition position. -/
theorem BungeDiagram.toFunctor_composition {α : Type u} [ActsOn α] (d : BungeDiagram α) :
    d.toFunctor.obj .composition = ↥d.system.composition := rfl

/-- The functor assigns the environment subtype to the environment position. -/
theorem BungeDiagram.toFunctor_environment {α : Type u} [ActsOn α] (d : BungeDiagram α) :
    d.toFunctor.obj .environment = ↥d.system.environment := rfl

/-- The functor assigns the structure subtype to the structure position. -/
theorem BungeDiagram.toFunctor_structure {α : Type u} [ActsOn α] (d : BungeDiagram α) :
    d.toFunctor.obj .structure' = ↥d.system.structure' := rfl
