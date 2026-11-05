/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic
import Systems.Category.ShapeMobus
import Systems.Tools.Atlas

/-!
# Shape Category for Mobus's published 7-Tuple (2022)

The *shape category* `I_Mobus2022` encodes the dependency structure of the
system definition Mobus publishes in *Systems Science: Theory, Analysis,
Modeling, and Design* (2022), ch. 4, §4.3.3, eq. (4.1), p. 191:

> a system S is a 7-tuple: Sᵢ,ₗ = C, N, G, B, T, H, Δtᵢ,ₗ

There is no environment coordinate. The book revisions (2024, Eq. 1) add E
as the eighth, and that revised tuple is what `ShapeMobus.lean` encodes
(atlas entry `mobus-revisions-oct-tuple`). This file encodes the published
seven, so the 2022 definition has its own counterpart (atlas entry
`mobus-2022-seven-tuple`).

## The owed debt (atlas mapping 005, `atlas/mappings/mobus-revision.md`)

The mapping records that "the 7-tuple embeds in the 8-tuple" had no theorem,
because the 2022 tuple had no shape by design, and proposes the discharge:
encode the 2022 tuple as its own shape and exhibit the inclusion functor
`mobus2022ToMobus : Paths Mobus2022Position ⥤ Paths MobusPosition`. That is
what this file does. The inclusion is injective on objects
(`mobus2022ToMobus_obj_injective`), which is the formal content of the
mapping's claim that nothing the 2022 definition asserts is withdrawn: every
position and every dependency of the seven survives in the eight.

## Construction

The seven positions are the eight of `MobusPosition` minus `environment`.
The generating arrows are those of `MobusArrow` that touch neither end at
`environment`: of the five revised arrows, `external_on_env` and
`env_disjoint_comp` fall away, three remain. The provenance of each is as in
`ShapeMobus.lean`; the coherence constraints they trace to (`network_components`,
`interfaces_sub`, `externalFlows_nodes` on the boundary side) are stated
without reference to E.

## Isolated Vertices

`transforms`, `history` and `timeScale`, as in the revised shape.
-/

/-- The seven positions in Mobus's published system tuple
S = (C, N, G, B, T, H, Δt) (2022, eq. 4.1).

- `components`: C — the set of active components
- `internalNetwork`: N — the directed graph of internal flows among components
- `externalFlows`: G — the bipartite flow graph crossing the boundary
- `boundary`: B — interface components and their properties
- `transforms`: T — domain-specific processing functions
- `history`: H — stored knowledge / memory
- `timeScale`: Δt — temporal resolution of observation

These are `MobusPosition` without `environment`; `Mobus2022Position.toMobus`
is the inclusion. -/
inductive Mobus2022Position
  | components
  | internalNetwork
  | externalFlows
  | boundary
  | transforms
  | history
  | timeScale
  deriving DecidableEq, Inhabited

/-- Generating morphisms for the 2022 Mobus shape quiver: the arrows of the
revised quiver (`MobusArrow`) that do not touch `environment`.

- `network_on_components`: N depends on C (internal network nodes = components)
- `interfaces_in_components`: B depends on C (interface components ⊆ components)
- `external_on_boundary`: G depends on B (external flow nodes include boundary interfaces)

Absent, because one end is E: `external_on_env` and `env_disjoint_comp`. -/
inductive Mobus2022Arrow : Mobus2022Position → Mobus2022Position → Type
  | network_on_components : Mobus2022Arrow .internalNetwork .components
  | interfaces_in_components : Mobus2022Arrow .boundary .components
  | external_on_boundary : Mobus2022Arrow .externalFlows .boundary

instance : Quiver Mobus2022Position where
  Hom := Mobus2022Arrow

open CategoryTheory in
/-- The shape category for Mobus's published 7-tuple (2022, eq. 4.1): the free
category on the coherence quiver without an environment vertex.

Seven objects, three generating arrows, a dependency DAG rooted at `components`;
`transforms`, `history`, `timeScale` isolated. -/
@[atlas "mobus-2022-seven-tuple"]
abbrev Mobus2022Shape := Paths Mobus2022Position

-- ═══════════════════════════════════════════════════════════════════════════════
-- § The inclusion 2022 → revised: the debt of mapping 005 discharged
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Each 2022 position is the revised position of the same name. -/
def Mobus2022Position.toMobus : Mobus2022Position → MobusPosition
  | .components => .components
  | .internalNetwork => .internalNetwork
  | .externalFlows => .externalFlows
  | .boundary => .boundary
  | .transforms => .transforms
  | .history => .history
  | .timeScale => .timeScale

open CategoryTheory in
/-- The inclusion prefunctor: positions to the positions of the same name,
each 2022 arrow to the revised arrow of the same name. -/
def mobus2022ToMobusPre : Prefunctor Mobus2022Position (Paths MobusPosition) where
  obj := fun p => p.toMobus
  map
    | .network_on_components => Quiver.Hom.toPath MobusArrow.network_on_components
    | .interfaces_in_components => Quiver.Hom.toPath MobusArrow.interfaces_in_components
    | .external_on_boundary => Quiver.Hom.toPath MobusArrow.external_on_boundary

open CategoryTheory in
/-- The inclusion functor `I_Mobus2022 → I_Mobus`, the one mapping 005 names as
the discharge of its debt: the published seven-tuple embeds in the revised eight. -/
def mobus2022ToMobus : Paths Mobus2022Position ⥤ Paths MobusPosition :=
  Paths.lift mobus2022ToMobusPre

/-- The inclusion is injective on objects: distinct 2022 positions go to distinct
revised positions, since each is sent to its namesake. Proved as the
`klirTo*_obj_injective` theorems of `CommonCore.lean` are: by cases on both
positions. -/
theorem mobus2022ToMobus_obj_injective : Function.Injective mobus2022ToMobusPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [mobus2022ToMobusPre, Mobus2022Position.toMobus]

/-- No 2022 position is sent to `environment`: the inclusion misses exactly the
coordinate the revision added. -/
theorem mobus2022ToMobus_ne_environment (p : Mobus2022Position) :
    mobus2022ToMobusPre.obj p ≠ MobusPosition.environment := by
  cases p <;> simp [mobus2022ToMobusPre, Mobus2022Position.toMobus]
