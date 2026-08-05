/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic
import Systems.Category.ShapeKlir

/-!
# Shape Category for Bertalanffy's General System Theory

The *shape category* `I_Bertalanffy` encodes the dependency structure of Bertalanffy's
verbal definition of "system".

## Source

Bertalanffy (1968), *General System Theory*, ch. 3 "Some System Concepts", p. 55:

> "A system can be defined as a complex of interacting elements. Interaction means that
> elements, p, stand in relations, R, so that the behavior of an element p in R is different
> from its behavior in another relation, R'."

Two positions are named in that sentence — the elements `p` and the relations `R` — and one
dependency: the relations are *on* the elements.

## Arrow direction — DECLARED, not assumed

`interrelation_on_elements : interrelation ⟶ elements`, read aloud: **"the interrelation
depends on the elements"** — you cannot state R without already having the p's it holds
between. This is the same convention as every other shape in this development (Klir's
`relation_on_things`, Mobus's `network_on_components`): an arrow points from the dependent
position to the position it depends on. It is NOT a function arrow and NOT a flow arrow.

## What this shape does NOT capture — the predicate gap

Bertalanffy's interaction clause carries a condition Klir's `S = (T, R)` does not: the
behaviour of an element **must differ** across relations. That is a predicate constraining
which R qualify, not a position and not a dependency, so the quiver cannot express it and
`bertalanffyToKlir` below discards it. The two definitions therefore have isomorphic shapes
(`shapeIso`) while making *different* demands — the shape functor is not injective on
definitional content.

This is a limit of the shape method, exhibited rather than asserted: `shapeIso` proves the
structures correspond, and this paragraph names exactly what survives the correspondence and
what does not. Compare Bunge's near-identical difference-making test — "unlike a mere
relation, a connection makes some difference to its relata" (1979, ch. 1 §1.2) — which Bunge
*does* promote to definitional force via the nonempty-bondage requirement, and which
`ShapeBunge` likewise cannot see.

## The 1972 restatement is a different shape

Bertalanffy (1972), "The History and Status of General Systems Theory", *Academy of
Management Journal* 15(4), p. 417, adds a third position:

> "A system may be defined as a set of elements standing in interrelation among themselves
> **and with the environment**."

That definition would carry a second arrow (`interrelation ⟶ environment`) and is deliberately
NOT encoded here — this file is the 1968 shape. The 1968 → 1972 pair is a definition revising
itself, and the two shapes are the record of what the revision changed.
-/

/-- The two positions in Bertalanffy's 1968 definition.

- `elements`: p — the elements composing the complex
- `interrelation`: R — the relations in which those elements stand
-/
inductive BertalanffyPosition
  | elements
  | interrelation
  deriving DecidableEq, Inhabited

/-- The single generating morphism.

`interrelation_on_elements`: R depends on p — "elements, p, stand in relations, R", so the
relations are defined over the elements and cannot be stated without them. -/
inductive BertalanffyArrow : BertalanffyPosition → BertalanffyPosition → Type
  | interrelation_on_elements : BertalanffyArrow .interrelation .elements

instance : Quiver BertalanffyPosition where
  Hom := BertalanffyArrow

open CategoryTheory in
/-- The shape category for Bertalanffy's 1968 definition: the free category on the
dependency quiver. Two objects, one generating arrow — the walking arrow. -/
abbrev BertalanffyShape := Paths BertalanffyPosition

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Bertalanffy and Klir have the same shape
-- ═══════════════════════════════════════════════════════════════════════════════

open CategoryTheory

/-!
Klir's `S = (T, R)` with `relation_on_things` and Bertalanffy's "complex of interacting
elements" with `interrelation_on_elements` are the same quiver under the evident renaming.
Two traditions — analytic-biological organicism (1968) and information-theoretic systems
science (2001, itself descending from 1969) — arrived at the same minimal dependency
structure independently.

Read the caveat above before quoting this: identical shape does NOT mean identical
definition.
-/

/-- The positions correspond: elements ↔ things, interrelation ↔ relation. -/
def positionEquiv : BertalanffyPosition ≃ KlirPosition where
  toFun := fun p => match p with
    | .elements => .things
    | .interrelation => .relation
  invFun := fun p => match p with
    | .things => .elements
    | .relation => .interrelation
  left_inv := by intro a; cases a <;> rfl
  right_inv := by intro a; cases a <;> rfl

/-- Bertalanffy's shape into Klir's: elements ↦ things, interrelation ↦ relation. -/
def bertalanffyToKlirPre : Prefunctor BertalanffyPosition (Paths KlirPosition) where
  obj := fun p => match p with
    | .elements => .things
    | .interrelation => .relation
  map := fun a => match a with
    | .interrelation_on_elements => Quiver.Hom.toPath KlirArrow.relation_on_things

/-- Klir's shape into Bertalanffy's: things ↦ elements, relation ↦ interrelation. -/
def klirToBertalanffyPre : Prefunctor KlirPosition (Paths BertalanffyPosition) where
  obj := fun p => match p with
    | .things => .elements
    | .relation => .interrelation
  map := fun a => match a with
    | .relation_on_things => Quiver.Hom.toPath BertalanffyArrow.interrelation_on_elements

theorem bertalanffyToKlir_obj_injective : Function.Injective bertalanffyToKlirPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [bertalanffyToKlirPre]

theorem klirToBertalanffy_obj_injective : Function.Injective klirToBertalanffyPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [klirToBertalanffyPre]

/-- The two object maps are mutually inverse: the embedding is an isomorphism on positions,
not merely an injection. This is what distinguishes Bertalanffy from the eight shapes
`CommonCore` embeds Klir *into* — there the embedding is proper, here it is onto. -/
theorem bertalanffyToKlir_obj_eq_equiv :
    bertalanffyToKlirPre.obj = positionEquiv := by
  funext p; cases p <;> rfl

theorem klirToBertalanffy_obj_eq_symm :
    klirToBertalanffyPre.obj = positionEquiv.symm := by
  funext p; cases p <;> rfl

/-- Round trip on objects, Bertalanffy → Klir → Bertalanffy, is the identity. -/
theorem obj_roundtrip (p : BertalanffyPosition) :
    klirToBertalanffyPre.obj (bertalanffyToKlirPre.obj p) = p := by
  cases p <;> rfl

/-- Round trip on objects, Klir → Bertalanffy → Klir, is the identity. -/
theorem obj_roundtrip' (p : KlirPosition) :
    bertalanffyToKlirPre.obj (klirToBertalanffyPre.obj p) = p := by
  cases p <;> rfl

/-- Each quiver has exactly one generating arrow, and the renaming matches them. Together
with `obj_roundtrip`/`obj_roundtrip'` this is the quiver isomorphism in elementary form. -/
theorem arrow_unique (a b : BertalanffyPosition) (f g : BertalanffyArrow a b) : f = g := by
  cases f; cases g; rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Obstruction audit (required of every new entry since the 2026-07-25 correction)
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
`SharedPrimitive.connected_is_single_arrow` — the repaired, quiver-level replacement for the
refuted maximality claim — is **target-dependent**: it is forced by Q_Joslyn (no out-degree
two) and Q_Willems (no in-degree two, no composable pair). Adding an entry can therefore
weaken it if the new quiver is permissive enough to readmit a competitor, so a new entry owes
an explicit check against the fork, cofork, and two-chain obstructions rather than an
assurance of neutrality.

Q_Bertalanffy is the most restrictive quiver that can appear: it *is* the shared primitive.
All four obstructions are proved below, so the entry cannot weaken the result — it has no
room to admit anything Q_Klir does not already admit.
-/

/-- No fork: every vertex has out-degree at most one. -/
theorem bertalanffy_out_degree_le_one {a b c : BertalanffyPosition}
    (e : BertalanffyArrow a b) (f : BertalanffyArrow a c) : b = c := by
  cases e <;> cases f <;> rfl

/-- No cofork: every vertex has in-degree at most one. -/
theorem bertalanffy_in_degree_le_one {a b c : BertalanffyPosition}
    (e : BertalanffyArrow a c) (f : BertalanffyArrow b c) : a = b := by
  cases e <;> cases f <;> rfl

/-- No two-chain: the single arrow ends at a sink, so no two edges compose. -/
theorem bertalanffy_no_composable {a b c : BertalanffyPosition}
    (e : BertalanffyArrow a b) (f : BertalanffyArrow b c) : False := by
  cases e <;> cases f

/-- No parallel edges. -/
theorem bertalanffy_no_parallel {a b : BertalanffyPosition}
    (e f : BertalanffyArrow a b) : e = f := by
  cases e <;> cases f <;> rfl
