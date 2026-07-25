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
import Systems.Category.ShapeSpivak
import Systems.Category.ShapeWillems

/-!
# The Common Core: I_Klir Embeds into Every Shape Category

The common core of all eight systems traditions is `I_Klir` — the walking arrow
category S = (T, R) with a single dependency R → T.

## Theorem

1. **Existence** (proven): eight embedding functors `I_Klir → I_X`, each injective
   on objects (`klirTo*_obj_injective`) and faithful (`klirTo*_faithful`).

2. **Maximality** (OPEN — the statement below is false as written):

   > "`I_Klir` is the largest connected category admitting a faithful functor into
   > every `I_X`."

   Counterexample. Take the three-object chain `a → b → c`, which is thin and
   connected, and send `a ↦ things`, `b ↦ things`, `c ↦ relation`... more simply,
   map it into `2` collapsing two objects. Composition is preserved, every hom-set
   of the chain is a singleton, so the functor is faithful. A category strictly
   larger than `I_Klir` therefore embeds faithfully into `I_Klir`.

   The defect is that faithfulness constrains hom-sets, not objects, so it cannot
   support "largest". Strengthening to *faithful and injective on objects* is
   necessary but **not sufficient**: the fork shape (one source, two arrows, two
   sinks) still embeds into all eight that way, entering Joslyn through the path
   `controller → effector → controlled`. That is machine-checked in
   `Systems/Category/SharedPrimitive.lean` (`free_category_maximality_fails`).

   The claim is true one level down, on the generating quivers rather than their
   free categories, where derived composites stop counting. See
   `SharedPrimitive.lean` for the repaired statement, the two obstructions that
   force it (Joslyn's out-degree and Willems' in-degree and lack of composables),
   and the sensitivity caveat that comes with working at that level.

## Systems-Theoretic Meaning

The one structural commitment shared by every tradition from Mesarović (1964)
through Spivak (2026): **a system has things and relations among them, and the
relations depend on the things.**

Everything else — environment, boundary, state, input, output, time, mechanism,
feedback, history — is tradition-specific elaboration. The elaborations cluster
into two families:
- **Structural/inward** (Bunge, Mobus): arrows converge toward components
- **Operational/outward** (Myers, Wymore, Mesarović): arrows radiate from state

Klir sits at the root of both families. The `rfl` proofs of the commuting triangle
(`KlirSystem.lean`) already showed both traditions produce the same (T, R) when
projected. The common-core theorem shows this convergence is UNIVERSAL — not just
Bunge and Mobus, but all eight traditions independently embed the walking arrow.
(Independence caveat for the eighth: Spivak shares community and lens machinery
with Myers — see `ShapeSpivak.lean`.)

## Embedding Table

| Target | things ↦ | relation ↦ | arrow ↦ |
|--------|----------|------------|---------|
| I_Bunge | composition | structure' | struct_on_comp |
| I_Mobus | components | internalNetwork | network_on_components |
| I_Myers | output | state | expose |
| I_Wymore | output | state | readout |
| I_Mesarovic | output | globalState | response_output |
| I_Joslyn | controlled | effector | efferent |
| I_Spivak | output | parameter | expose |
| I_Willems | signal | behavior | evaluate |

Willems row: LAYERED STATUS — kernel-neutrality witness, not counted in the
eight-traditions headline. The embedding (`klirToWillems`, ShapeWillems.lean)
shows the tradition most hostile to I/O orientation still carries the
predication arrow. But as a shape I_Willems is isomorphic to I_Mesarovic
(`willemsToMesarovic`), so a ninth-tradition claim would assert independence
on the one measure — single-system shape — where Willems provably collapses.
Willems' genuine independence lives at the composition layer (SSF #16),
which this table does not measure. The headline stays eight.
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

/-- Embedding I_Klir into I_Spivak: things ↦ output, relation ↦ parameter.
The output map f⁺ (parameter determines output) is the Klir arrow —
the identical pattern to the Myers embedding. -/
def klirToSpivakPre : Prefunctor KlirPosition (Paths SpivakPosition) where
  obj | .things => .output | .relation => .parameter
  map | .relation_on_things => Quiver.Hom.toPath SpivakArrow.expose

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
def klirToSpivak : Paths KlirPosition ⥤ Paths SpivakPosition :=
  Paths.lift klirToSpivakPre

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

theorem klirToSpivak_obj_injective : Function.Injective klirToSpivakPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [klirToSpivakPre]

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

/-- There is no path from `things` to `relation`.
Things is a sink: no arrow in the Klir quiver targets `relation`. -/
theorem klir_no_path_things_relation
    (p : Quiver.Path KlirPosition.things KlirPosition.relation) : False := by
  cases p with
  | cons _ e => exact nomatch e

/-- Every hom-set of `I_Klir` is a subsingleton: the four cases are
`{id}`, `∅`, `{relation_on_things}`, `{id}`. -/
theorem klir_path_subsingleton :
    ∀ (a b : KlirPosition) (p q : Quiver.Path a b), p = q := by
  intro a b p q
  cases a <;> cases b
  · rw [klir_things_self p, klir_things_self q]
  · exact (klir_no_path_things_relation p).elim
  · rw [klir_hom_unique p, klir_hom_unique q]
  · rw [klir_relation_self p, klir_relation_self q]

instance klirHomSubsingleton (X Y : Paths KlirPosition) : Subsingleton (X ⟶ Y) :=
  ⟨klir_path_subsingleton X Y⟩

/-- A functor out of a thin category is faithful: injectivity on a subsingleton
hom-set is vacuous. This is a property of the *source*, so it holds for every
functor out of `I_Klir` regardless of target. -/
theorem faithful_of_subsingleton_hom {C : Type*} [Category C] {D : Type*} [Category D]
    [∀ X Y : C, Subsingleton (X ⟶ Y)] (F : C ⥤ D) : F.Faithful :=
  ⟨fun _ => Subsingleton.elim _ _⟩

-- The eight embeddings are faithful. Note what this does and does not say: it is a
-- consequence of `I_Klir` being thin, not evidence about the target traditions. The
-- content of the common-core claim lives in object-injectivity above, which is what
-- rules out the degenerate embeddings that collapse `things` and `relation`.

theorem klirToBunge_faithful : klirToBunge.Faithful := faithful_of_subsingleton_hom _
theorem klirToMobus_faithful : klirToMobus.Faithful := faithful_of_subsingleton_hom _
theorem klirToMyers_faithful : klirToMyers.Faithful := faithful_of_subsingleton_hom _
theorem klirToWymore_faithful : klirToWymore.Faithful := faithful_of_subsingleton_hom _
theorem klirToMesarovic_faithful : klirToMesarovic.Faithful := faithful_of_subsingleton_hom _
theorem klirToJoslyn_faithful : klirToJoslyn.Faithful := faithful_of_subsingleton_hom _
theorem klirToSpivak_faithful : klirToSpivak.Faithful := faithful_of_subsingleton_hom _
theorem klirToWillems_faithful : klirToWillems.Faithful := faithful_of_subsingleton_hom _

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Maximality — OPEN
--
-- See the module docstring: the maximality statement is false under faithfulness
-- alone, and the repair (faithful AND injective on objects) is not yet formalized.
-- What follows is the object bound, which the repaired statement would use. It is
-- a fact about KlirPosition, not a maximality theorem, and should not be cited as
-- one.
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
