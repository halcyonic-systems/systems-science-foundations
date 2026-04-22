/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic
import Systems.Category.ShapeBunge
import Systems.Category.ShapeMobus

/-!
# Comparison Functor: I_Mobus → I_Bunge

The comparison functor maps the Mobus shape category to the Bunge shape category,
formalizing at the schema level what `MobusSystem.toBunge` does at the data level.

## Key Results

- The functor exists (by construction via `Paths.lift`)
- It is NOT injective on objects: multiple Mobus positions collapse
- Two collapse patterns emerge:
  - **Spatial factoring:** `internalNetwork` and `externalFlows` both map to `structure'`
  - **Temporal discarding:** `transforms`, `history`, `timeScale` collapse to `composition`
- One generating arrow is annihilated (maps to identity)
- Two generating arrows collapse (map to the same Bunge arrow)

These formally diagnose that Mobus *decomposes* what Bunge *unifies*.
-/

open CategoryTheory

/-- Object-level comparison: where each Mobus position lands in the Bunge schema.

Follows the `toBunge` bridge map:
- `components → composition` and `environment → environment` are canonical
- `internalNetwork, externalFlows → structure'` (both contribute to `totalRelation`)
- `boundary → composition` (interfaces are a subset of components)
- `transforms, history, timeScale → composition` (no Bunge counterpart; parametric discard)
-/
def comparisonObj : MobusPosition → BungePosition
  | .components       => .composition
  | .environment      => .environment
  | .internalNetwork  => .structure'
  | .externalFlows    => .structure'
  | .boundary         => .composition
  | .transforms       => .composition
  | .history          => .composition
  | .timeScale        => .composition

/-- The comparison as a prefunctor into the Bunge path category.

Each generating Mobus arrow maps to either a length-1 path (a generating Bunge arrow)
or a length-0 path (identity, when source and target collapse to the same Bunge position).
-/
def comparisonPre : Prefunctor MobusPosition (Paths BungePosition) where
  obj := comparisonObj
  map := fun
    | .network_on_components    => Quiver.Hom.toPath BungeArrow.struct_on_comp
    | .interfaces_in_components => Quiver.Path.nil
    | .external_on_env          => Quiver.Hom.toPath BungeArrow.struct_on_env
    | .external_on_boundary     => Quiver.Hom.toPath BungeArrow.struct_on_comp
    | .env_disjoint_comp        => Quiver.Hom.toPath BungeArrow.env_acts_on_comp

/-- The comparison functor from I_Mobus to I_Bunge, constructed via the universal property
of the free category. Any prefunctor from a quiver into a category lifts uniquely to a
functor from the path category. -/
def comparisonFunctor : Paths MobusPosition ⥤ Paths BungePosition :=
  Paths.lift comparisonPre

-- § Object-level characterization

theorem comparisonFunctor_obj (p : MobusPosition) :
    comparisonFunctor.obj p = comparisonObj p := rfl

-- § Information loss: object collapse

/-- Spatial factoring: internal network and external flows both map to structure. -/
theorem obj_collapse_network_external :
    comparisonObj .internalNetwork = comparisonObj .externalFlows := rfl

/-- Boundary collapses into composition (interfaces ⊆ components). -/
theorem obj_collapse_boundary :
    comparisonObj .boundary = comparisonObj .components := rfl

/-- Temporal discarding: transforms, history, and timeScale all collapse to composition. -/
theorem obj_collapse_parametric :
    comparisonObj .transforms = comparisonObj .history ∧
    comparisonObj .history = comparisonObj .timeScale ∧
    comparisonObj .timeScale = comparisonObj .components :=
  ⟨rfl, rfl, rfl⟩

-- § Information loss: arrow behavior

/-- Arrow collapse: two distinct Mobus arrows map to the same Bunge path.
`network_on_components` (N → C) and `external_on_boundary` (G → B) both become
`struct_on_comp` (S → C) in the Bunge shape. -/
theorem arrow_collapse :
    comparisonPre.map MobusArrow.network_on_components =
    comparisonPre.map MobusArrow.external_on_boundary := rfl

/-- Arrow annihilation: `interfaces_in_components` (B → C) maps to the identity path.
Both source (boundary) and target (components) map to `composition`, so the dependency
arrow is absorbed into the identity. -/
theorem arrow_annihilated :
    comparisonPre.map MobusArrow.interfaces_in_components = Quiver.Path.nil := rfl

-- § Non-injectivity (the punchline)

/-- The comparison is not injective on objects. This is the categorical content of
information loss: the Bunge schema cannot distinguish fields that Mobus keeps separate. -/
theorem comparisonObj_not_injective : ¬ Function.Injective comparisonObj := by
  intro h
  exact absurd (h (show comparisonObj .internalNetwork = comparisonObj .externalFlows from rfl))
    (by exact MobusPosition.noConfusion)

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Divergence Catalogue
--
-- Cross-reference with `Bridge.lean` six information-loss categories:
--   #1 Milieu μ (within E)    — invisible at shape level (intra-position data loss)
--   #2 Capacity κ (within G)  — invisible at shape level (intra-position data loss)
--   #3 Boundary props π       — shape: B collapses to C (obj_collapse_boundary)
--   #4 Transforms τ           — shape: T collapses to C (obj_collapse_parametric)
--   #5 History η              — shape: H collapses to C (obj_collapse_parametric)
--   #6 Time scale δ           — shape: Δt collapses to C (obj_collapse_parametric)
--
-- Categories #1-#2 are WITHIN-position losses (data inside a position is simplified
-- when projected). Categories #3-#6 are BETWEEN-position losses (entire positions
-- collapse onto another). The shape-level catalogue captures #3-#6; detecting
-- #1-#2 requires looking inside the diagram functor values.
-- ═══════════════════════════════════════════════════════════════════════════��═══

-- § Fiber characterization: which Mobus positions map to each Bunge position

/-- Fiber over `composition`: 5 Mobus positions collapse here.
Corresponds to Bridge.lean categories #3 (boundary), #4 (transforms), #5 (history), #6 (timeScale),
plus the canonical `components` mapping. -/
theorem fiber_composition (p : MobusPosition) :
    comparisonObj p = .composition ↔
    p = .components ∨ p = .boundary ∨ p = .transforms ∨
    p = .history ∨ p = .timeScale := by
  cases p <;> simp [comparisonObj]

/-- Fiber over `environment`: singleton (1:1 preservation).
Bridge.lean's info loss #1 (milieu μ) is invisible here — it occurs WITHIN the environment
position, not between positions. -/
theorem fiber_environment (p : MobusPosition) :
    comparisonObj p = .environment ↔ p = .environment := by
  cases p <;> simp [comparisonObj]

/-- Fiber over `structure'`: 2 Mobus positions collapse here.
Corresponds to the spatial factoring N + G → S. Bridge.lean's info loss #2 (capacity κ)
is invisible here — it occurs WITHIN the flow positions when `toRelation` discards κ. -/
theorem fiber_structure (p : MobusPosition) :
    comparisonObj p = .structure' ↔
    p = .internalNetwork ∨ p = .externalFlows := by
  cases p <;> simp [comparisonObj]

-- § Arrow-level divergence

/-- Every Bunge generating arrow has at least one Mobus preimage.
The comparison is surjective on generators (no Bunge dependency is "invented"). -/
theorem generators_surjective :
    (∃ f : MobusArrow .internalNetwork .components,
      comparisonPre.map f = Quiver.Hom.toPath BungeArrow.struct_on_comp) ∧
    (∃ f : MobusArrow .externalFlows .environment,
      comparisonPre.map f = Quiver.Hom.toPath BungeArrow.struct_on_env) ∧
    (∃ f : MobusArrow .environment .components,
      comparisonPre.map f = Quiver.Hom.toPath BungeArrow.env_acts_on_comp) :=
  ⟨⟨.network_on_components, rfl⟩, ⟨.external_on_env, rfl⟩, ⟨.env_disjoint_comp, rfl⟩⟩

/-- The comparison functor is NOT full: there exist Bunge morphisms between image
objects with no Mobus preimage in the corresponding hom-set.

Witness: the composite path S → E → C (length 2) in I_Bunge lives in
Hom(structure', composition). But the only Mobus path from internalNetwork to
components is `network_on_components` (length 1), whose image is the direct
`struct_on_comp` (length 1). The length-2 path has no preimage from that hom-set. -/
theorem comparisonFunctor_not_full :
    ∃ (f : comparisonFunctor.obj (.internalNetwork : Paths MobusPosition) ⟶
           comparisonFunctor.obj (.components : Paths MobusPosition)),
      f.length = 2 ∧
      (comparisonFunctor.map (Quiver.Hom.toPath MobusArrow.network_on_components)).length = 1 := by
  exact ⟨(Quiver.Hom.toPath BungeArrow.struct_on_env).cons BungeArrow.env_acts_on_comp,
         rfl, rfl⟩
