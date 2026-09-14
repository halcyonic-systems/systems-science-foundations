/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Systems.Category.ShapeRosen
import Systems.Category.CommonCore

/-!
# Rosen's (S, F) and the walking arrow are the same shape (mapping 008, claim 1)

Definition 2.9.1 of Rosen 1978, encoded as in `ShapeRosen.lean` (ℝ as
substrate, not position), has the dependency quiver `observables → states`.
Klir's S = (T, R) has `relation → things`. Both are the walking arrow, and
this file exhibits the equivalence of the two free categories in both
directions with both round trips equal to the identity — an isomorphism of
categories, not merely a faithful embedding one way.

What this does and does not say. It says: on the stated encoding, the
*dependency shape* of Rosen's formal-system definition is the K ≅ 2 kernel's
shape, position for position (states ↔ things, observables ↔ relation). It does
not say the two definitions mean the same thing: Klir's relata are things and
his R is a relation on them; Rosen's relata are the states of ONE system and his
F is a family of functions out of them. The forced assignment `things ↦ states`
is the cost mapping 008 names as "states stand in for things", and it is a
statement about the encoding, not a discovery about Rosen. Presentation-
relative, as every shape result here is: on the cospan encoding (ℝ as a
position) the equivalence fails on object count alone.
-/

open CategoryTheory

/-- Klir → Rosen: things ↦ states, relation ↦ observables. -/
def klirToRosenPre : Prefunctor KlirPosition (Paths RosenPosition) where
  obj | .things => .states | .relation => .observables
  map | .relation_on_things => Quiver.Hom.toPath RosenArrow.defined_on

/-- Rosen → Klir: states ↦ things, observables ↦ relation. -/
def rosenToKlirPre : Prefunctor RosenPosition (Paths KlirPosition) where
  obj | .states => .things | .observables => .relation
  map | .defined_on => Quiver.Hom.toPath KlirArrow.relation_on_things

def klirToRosen : Paths KlirPosition ⥤ Paths RosenPosition := Paths.lift klirToRosenPre
def rosenToKlir : Paths RosenPosition ⥤ Paths KlirPosition := Paths.lift rosenToKlirPre

theorem klirToRosen_obj_injective : Function.Injective klirToRosenPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [klirToRosenPre]

theorem rosenToKlir_obj_injective : Function.Injective rosenToKlirPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [rosenToKlirPre]

/-- Faithful in both directions, because both sources are thin. -/
theorem klirToRosen_faithful : klirToRosen.Faithful := faithful_of_subsingleton_hom _
theorem rosenToKlir_faithful : rosenToKlir.Faithful := faithful_of_subsingleton_hom _

/-- Round trip Klir → Rosen → Klir is the identity functor. -/
theorem klirToRosen_rosenToKlir : klirToRosen ⋙ rosenToKlir = 𝟭 (Paths KlirPosition) :=
  Paths.ext_functor (by funext x; cases x <;> rfl) (by intro a b e; cases e; rfl)

/-- Round trip Rosen → Klir → Rosen is the identity functor. -/
theorem rosenToKlir_klirToRosen : rosenToKlir ⋙ klirToRosen = 𝟭 (Paths RosenPosition) :=
  Paths.ext_functor (by funext x; cases x <;> rfl) (by intro a b e; cases e; rfl)

/-- **Mapping 008, claim 1.** Rosen's (S, F) shape and Klir's (T, R) shape are
equivalent categories, with both composites literally the identity — an
isomorphism of the two free categories. -/
def rosenKlirEquiv : Paths RosenPosition ≌ Paths KlirPosition :=
  CategoryTheory.Equivalence.mk rosenToKlir klirToRosen
    (eqToIso rosenToKlir_klirToRosen.symm)
    (eqToIso klirToRosen_rosenToKlir)
