/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Shape Category for Bunge's CES Framework

The *shape category* `I_Bunge` encodes the dependency structure of Bunge's
system definition σ = ⟨C, E, S⟩ (Treatise on Basic Philosophy Vol. 4, Def 1.2, 1979).

## Construction

We define a quiver with 3 vertices (the tuple positions) and 3 generating arrows
(the structural dependencies), then take the free category via `Paths`.

## Arrow Direction Convention

Arrows point from the *dependent* to what it *depends on*. This makes a system-as-diagram
(a functor from the shape category to a data category) covariant.

- S → C: structure is defined over composition
- S → E: structure is defined over environment
- E → C: environment acts on composition (Bunge's interaction axiom)
-/

/-- The three positions in Bunge's CES system definition.

- `composition`: C(σ,t) — the set of components
- `environment`: E(σ,t) — the set of environmental things
- `structure'`: S(σ,t) — the set of relations/bonds among components and environment
-/
inductive BungePosition
  | composition
  | environment
  | structure'
  deriving DecidableEq, Inhabited

/-- Generating morphisms for the Bunge shape quiver.

Each arrow encodes a structural dependency from Bunge Def 1.2:
- `struct_on_comp`: S is defined over C (Def 1.2iii: "relations among the components")
- `struct_on_env`: S is defined over E (Def 1.2iii: "among them and things in the environment")
- `env_acts_on_comp`: E constrains C (Def 1.2ii: things that "act on or are acted on by components")
-/
inductive BungeArrow : BungePosition → BungePosition → Type
  | struct_on_comp : BungeArrow .structure' .composition
  | struct_on_env : BungeArrow .structure' .environment
  | env_acts_on_comp : BungeArrow .environment .composition

instance : Quiver BungePosition where
  Hom := BungeArrow

open CategoryTheory in
/-- The shape category for Bunge's CES framework: the free category on the dependency quiver.

Morphisms are composable paths of generating arrows. In particular, `S → C` has two
distinct morphisms: the direct `struct_on_comp` and the composite `struct_on_env ≫ env_acts_on_comp`.
These correspond to two genuinely different structural dependencies in Bunge's theory. -/
abbrev BungeShape := Paths BungePosition
