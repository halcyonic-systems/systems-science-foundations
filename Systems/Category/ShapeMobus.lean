/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Shape Category for Mobus's 8-Tuple Framework

The *shape category* `I_Mobus` encodes the dependency structure of Mobus's
system definition S = (C, N, E, G, B, T, H, Δt).

## Construction

We define a quiver with 8 vertices (the tuple positions) and 5 generating arrows
(derived from the coherence constraints in `MobusSystem`), then take the free category.

## Arrow Provenance

Each generating arrow traces to a specific coherence constraint:
- `network_on_components` ← `network_components : N.nodes = C`
- `interfaces_in_components` ← `interfaces_sub : B.interfaces ⊆ C`
- `external_on_env` ← `externalFlows_nodes` (environment component)
- `external_on_boundary` ← `externalFlows_nodes` (boundary component)
- `env_disjoint_comp` ← `disjoint : C ∩ E.objects = ∅`

## Isolated Vertices

`transforms`, `history`, and `timeScale` have no generating arrows. They are
parametric data with no structural role in the coherence constraints.
-/

/-- The eight positions in Mobus's system tuple S = (C, N, E, G, B, T, H, Δt).

- `components`: C — the set of active components
- `internalNetwork`: N — the directed graph of internal flows among components
- `environment`: E — environmental objects and milieu
- `externalFlows`: G — the bipartite flow graph crossing the boundary
- `boundary`: B — interface components and their properties
- `transforms`: T — domain-specific processing functions
- `history`: H — stored knowledge / memory
- `timeScale`: Δt — temporal resolution of observation
-/
inductive MobusPosition
  | components
  | internalNetwork
  | environment
  | externalFlows
  | boundary
  | transforms
  | history
  | timeScale
  deriving DecidableEq, Inhabited

/-- Generating morphisms for the Mobus shape quiver.

Each arrow encodes a coherence constraint from the `MobusSystem` structure:
- `network_on_components`: N depends on C (internal network nodes = components)
- `interfaces_in_components`: B depends on C (interface components ⊆ components)
- `external_on_env`: G depends on E (external flow nodes include environment objects)
- `external_on_boundary`: G depends on B (external flow nodes include boundary interfaces)
- `env_disjoint_comp`: E constrains C (components and environment are disjoint)
-/
inductive MobusArrow : MobusPosition → MobusPosition → Type
  | network_on_components : MobusArrow .internalNetwork .components
  | interfaces_in_components : MobusArrow .boundary .components
  | external_on_env : MobusArrow .externalFlows .environment
  | external_on_boundary : MobusArrow .externalFlows .boundary
  | env_disjoint_comp : MobusArrow .environment .components

instance : Quiver MobusPosition where
  Hom := MobusArrow

open CategoryTheory in
/-- The shape category for Mobus's 8-tuple framework: the free category on the coherence quiver.

The 3 isolated vertices (transforms, history, timeScale) have only identity morphisms.
The 5 connected vertices form a dependency DAG rooted at `components`. -/
abbrev MobusShape := Paths MobusPosition
