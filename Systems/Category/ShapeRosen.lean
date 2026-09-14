/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Shape Category for Rosen's formal system (S, F)

The *shape category* `I_Rosen` encodes the dependency structure of Rosen's
Definition 2.9.1 (*Fundamentals of Measurement and Representation of Natural
Systems*, Elsevier North-Holland 1978, book p. 54; atlas entry 010):

> A system (or formal system) shall consist of a pair (S, F), where S is a set
> and F is a family of real-valued mappings defined on S. The elements of F
> will be called the observables of the formal system.

## Construction

- `states`: S — the set the definition calls "a set" and the gloss calls the
  states (Rosen's own word for the elements of S throughout ch. 2).
- `observables`: F — the family of observables.
- `defined_on`: F → S — "a family of real-valued mappings *defined on* S".

## The encoding decision (mapping 008, claim 1)

The real line is NOT a position. Proposition 2 (p. 26) fixes the codomain of
every observable as ℝ once and for all, so ℝ is part of the ambient substrate of
the definition, like `Set` for Klir, and not a relatum the definition varies
over. On this encoding the quiver has 2 objects and 1 arrow: it is the walking
arrow, and `RosenKlirIso.lean` proves it is equivalent to `KlirShape`.

The alternative encoding — ℝ as a third position with a second arrow
F → ℝ — gives a cospan `S ← F → ℝ`, not the arrow. That encoding is not
built here; mapping 008 records it as the presentation on which claim 1 would
fail. The choice is a reading of the text (Proposition 2 makes ℝ fixed), and
it is stated here so that the theorem downstream is read as relative to it.

## Arrow direction convention

Arrows point in the direction of dependency, as in `ShapeKlir`: `defined_on`
reads "F depends on S" (the observables are defined over the states). This is
the same convention as Klir's `relation_on_things` ("R is defined over T"),
which is what makes the two shapes comparable position-for-position.

## What the shape forgets

That the observables are real-valued (Proposition 2), that the states carry no
structure ("no further structure was assumed", p. 54), and the reduced-state
construction S/R_F. A quiver records that a dependency exists, nothing more.
-/

/-- The two positions in Rosen's formal system (S, F).

- `states`: S — the set of states
- `observables`: F — the family of real-valued mappings defined on S
-/
inductive RosenPosition
  | states
  | observables
  deriving DecidableEq, Inhabited

/-- The single generating morphism for the Rosen shape quiver.

`defined_on`: F depends on S — the observables are "defined on S". -/
inductive RosenArrow : RosenPosition → RosenPosition → Type
  | defined_on : RosenArrow .observables .states

instance : Quiver RosenPosition where
  Hom := RosenArrow

open CategoryTheory in
/-- The shape category for Rosen's (S, F): the free category on the one-arrow
dependency quiver. Two objects, one arrow — the walking arrow. -/
abbrev RosenShape := Paths RosenPosition

/-! ## Thinness

Every hom-set of `I_Rosen` is a subsingleton, by the same case analysis as
`I_Klir` (`CommonCore.lean`): `states` is a sink, nothing targets
`observables`, and the one non-identity hom-set is the generating arrow. -/

/-- Every self-path at `observables` is the identity: no arrow targets it. -/
theorem rosen_observables_self
    (p : Quiver.Path RosenPosition.observables RosenPosition.observables) :
    p = Quiver.Path.nil := by
  cases p with
  | nil => rfl
  | cons _ e => exact nomatch e

/-- Every self-path at `states` is the identity: `states` is a sink. -/
theorem rosen_states_self
    (p : Quiver.Path RosenPosition.states RosenPosition.states) :
    p = Quiver.Path.nil := by
  cases p with
  | nil => rfl
  | cons p e =>
    cases e with
    | defined_on =>
      cases p with
      | cons _ e' => exact nomatch e'

/-- Every path from `observables` to `states` is the generating arrow. -/
theorem rosen_hom_unique
    (p : Quiver.Path RosenPosition.observables RosenPosition.states) :
    p = Quiver.Hom.toPath RosenArrow.defined_on := by
  cases p with
  | cons p e =>
    cases e with
    | defined_on =>
      have h := rosen_observables_self p
      subst h; rfl

/-- There is no path from `states` to `observables`. -/
theorem rosen_no_path_states_observables
    (p : Quiver.Path RosenPosition.states RosenPosition.observables) : False := by
  cases p with
  | cons _ e => exact nomatch e

/-- Every hom-set of `I_Rosen` is a subsingleton. -/
theorem rosen_path_subsingleton :
    ∀ (a b : RosenPosition) (p q : Quiver.Path a b), p = q := by
  intro a b p q
  cases a <;> cases b
  · rw [rosen_states_self p, rosen_states_self q]
  · exact (rosen_no_path_states_observables p).elim
  · rw [rosen_hom_unique p, rosen_hom_unique q]
  · rw [rosen_observables_self p, rosen_observables_self q]

open CategoryTheory in
instance rosenHomSubsingleton (X Y : Paths RosenPosition) : Subsingleton (X ⟶ Y) :=
  ⟨rosen_path_subsingleton X Y⟩
