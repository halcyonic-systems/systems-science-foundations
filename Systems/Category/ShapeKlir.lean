/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Shape Category for Klir's S = (T, R)

The *shape category* `I_Klir` encodes the dependency structure of Klir's
system definition S = (T, R) (Facets of Systems Science, 2001, Eq. 1.1).

This is the simplest non-discrete shape category in the landscape:
2 objects and 1 generating arrow. It is the common ancestor of both
Bunge's CES triple and Mobus's 8-tuple — the `rfl` proofs of the
commuting triangle trace to both authors inheriting T as `Set α` and
R as `Set (α × α)` from Klir without changing the mathematical type.

## Construction

- `things`: T — the set of things (thinghood)
- `relation`: R — the set of relations on T (systemhood)
- `relation_on_things`: R → T — R is defined over T

A thing becomes a system when you specify which of its parts are related.
The single arrow captures this: the relation DEPENDS on the things.
-/

/-- The two positions in Klir's system definition S = (T, R).

- `things`: T — the set of things that constitute the system
- `relation`: R — the set of relations among those things
-/
inductive KlirPosition
  | things
  | relation
  deriving DecidableEq, Inhabited

/-- The single generating morphism for the Klir shape quiver.

`relation_on_things`: R depends on T — the relation is defined over the set of things.
This is the minimal structural commitment: to have a system, your relation
must refer to your things. -/
inductive KlirArrow : KlirPosition → KlirPosition → Type
  | relation_on_things : KlirArrow .relation .things

instance : Quiver KlirPosition where
  Hom := KlirArrow

open CategoryTheory in
/-- The shape category for Klir's S = (T, R): the free category on the minimal
dependency quiver. With 2 objects and 1 arrow, this is the walking arrow category —
the simplest non-discrete shape in the landscape.

Every other shape category in the landscape admits a comparison functor FROM this
shape (Klir embeds into all of them), making I_Klir a candidate for the common core. -/
abbrev KlirShape := Paths KlirPosition
