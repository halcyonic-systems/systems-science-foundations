/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Systems.Category.ShapeJoslyn
import Systems.Category.CyclicObstruction

/-!
# Joslyn's feedback shape is a boundary of the finite-shape method

`JoslynShape` is the free category on a *cyclic* quiver (the efferent/afferent
feedback loop between `effector` and `controlled`). Every other tradition in the
landscape (Klir, Bunge, Mobus, Myers, Wymore, Mesarovic) has a DAG-shaped
quiver, hence finite hom-sets, and admits comparison functors to and from the
kernel. Joslyn does not — and this file proves *why* the standard comparison
machinery cannot reach it: **no faithful functor from `JoslynShape` into any
category with finite hom-sets exists.**

The obstruction is the shared cyclic pigeonhole (`CyclicObstruction.lean`,
issue #21 route (a)): the feedback loop's powers are distinguished by length,
so `effector ⟶ effector` is infinite, and a faithful functor would inject it
into a finite hom-set. This file only exhibits the loop; the argument is
`paths_no_faithful_functor_of_cycle`, proved once for every cyclic shape
(Spivak's value-feedback cycle instantiates the same lemma in
`SpivakIncomparability.lean`).

This turns "Joslyn is categorically incomparable to the others by standard means"
(previously stated as folklore) into a theorem: feedback is a genuine boundary of
the finite-shape method, not a gap in effort.

**Engineering note (in `Paths V`, drive hom inference through `Quiver.Path`,
never through object ascription).** `Paths V := V`, and `V`'s own `Quiver`
instance shadows the path category, so `(x : Paths V)` collapses to `x : V` and
`x ⟶ x` grabs the raw quiver (`JoslynArrow`), not `Quiver.Path`. Naming
`F.map_injective`'s objects then demands a bogus `Category V`. The fix: feed an
explicitly `Quiver.Path`-typed term to `F.map` and let unification pin the
objects (now encapsulated inside `paths_no_faithful_functor_of_cycle`).
-/

open CategoryTheory Quiver

/-- The single efferent ∘ afferent feedback loop `effector ⟶ effector` —
the generating cycle of Joslyn's shape. Length 2. -/
def joslynLoop : Quiver.Path (JoslynPosition.effector) (JoslynPosition.effector) :=
  (Quiver.Path.nil.cons JoslynArrow.efferent).cons JoslynArrow.afferent

theorem joslynLoop_length : joslynLoop.length = 2 := rfl

/-- The feedback hom-set `effector ⟶ effector` is infinite. -/
instance : Infinite (Quiver.Path (JoslynPosition.effector) (JoslynPosition.effector)) :=
  infinite_path_of_cycle joslynLoop (by simp [joslynLoop_length])

/-- **Joslyn's feedback shape admits no faithful functor into any category with
finite hom-sets.** The feedback loop makes `effector ⟶ effector` infinite;
faithfulness would inject it into the finite hom-set of the target. -/
theorem joslyn_no_faithful_functor
    {C : Type*} [Category C] [∀ X Y : C, Finite (X ⟶ Y)]
    (F : JoslynShape ⥤ C) : ¬ F.Faithful :=
  paths_no_faithful_functor_of_cycle joslynLoop (by simp [joslynLoop_length]) F
