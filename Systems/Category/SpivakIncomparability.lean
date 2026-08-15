/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Systems.Category.ShapeSpivak
import Systems.Category.CyclicObstruction

/-!
# Spivak's value-feedback shape is a boundary of the finite-shape method

`SpivakShape` is the free category on a *cyclic* quiver: `drive` and
`potential_on_parameter` form the value-feedback cycle `parameter ⇄ potential`
(see `ShapeSpivak.lean`). This is the landscape's second cyclic shape — where
Joslyn's cycle is feedback through *observation*, Spivak's is feedback through
*value* — and it meets the identical obstruction: **no faithful functor from
`SpivakShape` into any category with finite hom-sets exists.**

The argument is the shared cyclic pigeonhole
(`paths_no_faithful_functor_of_cycle`, `CyclicObstruction.lean`); this file
only exhibits the loop. Together with `JoslynIncomparability.lean` this closes
issue #21: both feedback traditions are provably outside the finite-shape
comparison method, and the obstruction is structural (cyclicity ⇒ infinite
hom-sets), not a gap in effort.

Provenance: the direct-instance draft of this proof was produced by the Lea
proving agent (VIDA-NYU) driving a locally-hosted model against a sorry-stubbed
challenge file (2026-08-15 probe); statement authored and verified upstream,
then refactored by hand into the shared-lemma form the issue pre-registered.
-/

open CategoryTheory Quiver

/-- The single drive ∘ potential_on_parameter value-feedback loop
`parameter ⟶ parameter` — the generating cycle of Spivak's shape. Length 2. -/
def spivakLoop : Quiver.Path (SpivakPosition.parameter) (SpivakPosition.parameter) :=
  (Quiver.Path.nil.cons SpivakArrow.drive).cons SpivakArrow.potential_on_parameter

theorem spivakLoop_length : spivakLoop.length = 2 := rfl

/-- The value-feedback hom-set `parameter ⟶ parameter` is infinite. -/
instance : Infinite (Quiver.Path (SpivakPosition.parameter) (SpivakPosition.parameter)) :=
  infinite_path_of_cycle spivakLoop (by simp [spivakLoop_length])

/-- **Spivak's value-feedback shape admits no faithful functor into any category
with finite hom-sets.** The `drive` / `potential_on_parameter` cycle makes
`parameter ⟶ parameter` infinite; faithfulness would inject it into the finite
hom-set of the target. -/
theorem spivak_no_faithful_functor
    {C : Type*} [Category C] [∀ X Y : C, Finite (X ⟶ Y)]
    (F : SpivakShape ⥤ C) : ¬ F.Faithful :=
  paths_no_faithful_functor_of_cycle spivakLoop (by simp [spivakLoop_length]) F
