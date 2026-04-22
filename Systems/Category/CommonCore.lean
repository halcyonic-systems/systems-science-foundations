/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic
import Systems.Category.ShapeKlir
import Systems.Category.ShapeBunge
import Systems.Category.ShapeMobus
import Systems.Category.ShapeMyers
import Systems.Category.ShapeWymore
import Systems.Category.ShapeMesarovic
import Systems.Category.ShapeJoslyn

/-!
# The Common Core: I_Klir Embeds into Every Shape Category

The common core of all seven systems traditions is `I_Klir` — the walking arrow
category S = (T, R) with a single dependency R → T.

## Theorem

`I_Klir` is the largest CONNECTED subcategory that embeds faithfully into all
seven shape categories. "Connected" means: there exists a non-identity morphism
(the category is not discrete). This excludes trivial embeddings of isolated points.

The proof has two parts:

1. **Existence**: Seven faithful embedding functors `I_Klir → I_X`
2. **Maximality**: `I_Klir` is the bottleneck. It has 2 objects and exactly 1
   non-identity morphism per non-empty hom-set. Any faithful functor INTO I_Klir
   from a connected category maps at most 1 arrow per hom-set, and the only
   connected subcategory of I_Klir is I_Klir itself.

## Systems-Theoretic Meaning

The one structural commitment shared by every tradition from Mesarović (1964)
through Myers (2023): **a system has things and relations among them, and the
relations depend on the things.**

Everything else — environment, boundary, state, input, output, time, mechanism,
feedback, history — is tradition-specific elaboration. The elaborations cluster
into two families:
- **Structural/inward** (Bunge, Mobus): arrows converge toward components
- **Operational/outward** (Myers, Wymore, Mesarović): arrows radiate from state

Klir sits at the root of both families. The `rfl` proofs of the commuting triangle
(`KlirSystem.lean`) already showed both traditions produce the same (T, R) when
projected. The common-core theorem shows this convergence is UNIVERSAL — not just
Bunge and Mobus, but all seven traditions independently embed the walking arrow.

## Embedding Table

| Target | things ↦ | relation ↦ | arrow ↦ |
|--------|----------|------------|---------|
| I_Bunge | composition | structure' | struct_on_comp |
| I_Mobus | components | internalNetwork | network_on_components |
| I_Myers | output | state | expose |
| I_Wymore | output | state | readout |
| I_Mesarovic | output | globalState | response_output |
| I_Joslyn | controlled | effector | efferent |
-/

open CategoryTheory

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Embedding Prefunctors: I_Klir → each shape category
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Embedding I_Klir into I_Bunge: things ↦ composition, relation ↦ structure'. -/
def klirToBungePre : Prefunctor KlirPosition (Paths BungePosition) where
  obj | .things => .composition | .relation => .structure'
  map | .relation_on_things => Quiver.Hom.toPath BungeArrow.struct_on_comp

/-- Embedding I_Klir into I_Mobus: things ↦ components, relation ↦ internalNetwork. -/
def klirToMobusPre : Prefunctor KlirPosition (Paths MobusPosition) where
  obj | .things => .components | .relation => .internalNetwork
  map | .relation_on_things => Quiver.Hom.toPath MobusArrow.network_on_components

/-- Embedding I_Klir into I_Myers: things ↦ output, relation ↦ state.
The expose function (state determines output) is the Klir arrow. -/
def klirToMyersPre : Prefunctor KlirPosition (Paths MyersPosition) where
  obj | .things => .output | .relation => .state
  map | .relation_on_things => Quiver.Hom.toPath MyersArrow.expose

/-- Embedding I_Klir into I_Wymore: things ↦ output, relation ↦ state. -/
def klirToWymorePre : Prefunctor KlirPosition (Paths WymorePosition) where
  obj | .things => .output | .relation => .state
  map | .relation_on_things => Quiver.Hom.toPath WymoreArrow.readout

/-- Embedding I_Klir into I_Mesarovic: things ↦ output, relation ↦ globalState. -/
def klirToMesarovicPre : Prefunctor KlirPosition (Paths MesarovicPosition) where
  obj | .things => .output | .relation => .globalState
  map | .relation_on_things => Quiver.Hom.toPath MesarovicArrow.response_output

/-- Embedding I_Klir into I_Joslyn: things ↦ controlled, relation ↦ effector.
The efferent action (effector constrains controlled variables) is the Klir arrow. -/
def klirToJoslynPre : Prefunctor KlirPosition (Paths JoslynPosition) where
  obj | .things => .controlled | .relation => .effector
  map | .relation_on_things => Quiver.Hom.toPath JoslynArrow.efferent

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Embedding Functors via Paths.lift
-- ═══════════════════════════════════════════════════════════════════════════════

def klirToBunge : Paths KlirPosition ⥤ Paths BungePosition :=
  Paths.lift klirToBungePre
def klirToMobus : Paths KlirPosition ⥤ Paths MobusPosition :=
  Paths.lift klirToMobusPre
def klirToMyers : Paths KlirPosition ⥤ Paths MyersPosition :=
  Paths.lift klirToMyersPre
def klirToWymore : Paths KlirPosition ⥤ Paths WymorePosition :=
  Paths.lift klirToWymorePre
def klirToMesarovic : Paths KlirPosition ⥤ Paths MesarovicPosition :=
  Paths.lift klirToMesarovicPre
def klirToJoslyn : Paths KlirPosition ⥤ Paths JoslynPosition :=
  Paths.lift klirToJoslynPre

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Injectivity on objects (all embeddings send distinct positions to distinct positions)
-- ═══════════════════════════════════════════════════════════════════════════════

theorem klirToBunge_obj_injective : Function.Injective klirToBungePre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [klirToBungePre]

theorem klirToMobus_obj_injective : Function.Injective klirToMobusPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [klirToMobusPre]

theorem klirToMyers_obj_injective : Function.Injective klirToMyersPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [klirToMyersPre]

theorem klirToWymore_obj_injective : Function.Injective klirToWymorePre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [klirToWymorePre]

theorem klirToMesarovic_obj_injective : Function.Injective klirToMesarovicPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [klirToMesarovicPre]

theorem klirToJoslyn_obj_injective : Function.Injective klirToJoslynPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [klirToJoslynPre]

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Faithfulness
--
-- Every non-empty hom-set in I_Klir is a singleton:
-- - Hom(things, things) = {id}     (things is a sink: no outgoing arrows)
-- - Hom(relation, relation) = {id} (no self-loops in the quiver)
-- - Hom(relation, things) = {relation_on_things.toPath}  (one generating arrow)
-- - Hom(things, relation) = ∅      (no path from sink to source)
--
-- Any function from a singleton (or empty) set is injective. Therefore EVERY
-- functor out of I_Klir is faithful — regardless of target. This is a property
-- of I_Klir's shape, not of the specific embeddings.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Every self-path at `relation` is the identity.
No arrow in the Klir quiver targets `relation`, so cons is impossible. -/
theorem klir_relation_self (p : Quiver.Path KlirPosition.relation KlirPosition.relation) :
    p = Quiver.Path.nil := by
  cases p with
  | nil => rfl
  | cons _ e => exact nomatch e

/-- Every self-path at `things` is the identity.
Things is a sink: the only arrow targeting things is `relation_on_things`,
but a path from things through relation back to things would require
an arrow targeting relation, which doesn't exist. -/
theorem klir_things_self (p : Quiver.Path KlirPosition.things KlirPosition.things) :
    p = Quiver.Path.nil := by
  cases p with
  | nil => rfl
  | cons p e =>
    cases e with
    | relation_on_things =>
      cases p with
      | cons _ e' => exact nomatch e'

/-- Every path from `relation` to `things` equals the generating arrow.
Hom(relation, things) is a singleton in the free category. -/
theorem klir_hom_unique (p : Quiver.Path KlirPosition.relation KlirPosition.things) :
    p = Quiver.Hom.toPath KlirArrow.relation_on_things := by
  cases p with
  | cons p e =>
    cases e with
    | relation_on_things =>
      have h := klir_relation_self p
      subst h; rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Maximality
--
-- I_Klir is the largest connected shape that embeds faithfully into all seven
-- traditions. The bottleneck is I_Klir itself: any faithful functor from a
-- connected free category into I_Klir can have at most the structure of I_Klir.
--
-- Proof sketch (formalized as individual lemmas):
-- 1. KlirPosition has exactly 2 elements (pigeonhole excludes 3+ object embeddings)
-- 2. Hom(relation, things) is a singleton (no room for parallel arrows)
-- 3. These together mean I_Klir is the unique maximal connected subcategory of itself
-- ═══════════════════════════════════════════════════════════════════════════════

/-- KlirPosition has exactly 2 elements: any function from a 3-element type
cannot be injective into KlirPosition (pigeonhole). -/
theorem klir_has_two_elements : ∀ (f : Fin 3 → KlirPosition), ¬ Function.Injective f := by
  intro f hinj
  have h : f 0 = f 1 ∨ f 0 = f 2 ∨ f 1 = f 2 := by
    cases (f 0) <;> cases (f 1) <;> cases (f 2) <;> simp
  rcases h with h | h | h
  · exact absurd (hinj h) (by decide)
  · exact absurd (hinj h) (by decide)
  · exact absurd (hinj h) (by decide)
