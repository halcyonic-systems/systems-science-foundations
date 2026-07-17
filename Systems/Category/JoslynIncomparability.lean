/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Systems.Category.ShapeJoslyn
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.Data.Finite.Set

/-!
# Joslyn's feedback shape is a boundary of the finite-shape method

`JoslynShape` is the free category on a *cyclic* quiver (the efferent/afferent
feedback loop between `effector` and `controlled`). Every other tradition in the
landscape (Klir, Bunge, Mobus, Myers, Wymore, Mesarovic, Spivak) has a DAG-shaped
quiver, hence finite hom-sets, and admits comparison functors to and from the
kernel. Joslyn does not — and this file proves *why* the standard comparison
machinery cannot reach it: **no faithful functor from `JoslynShape` into any
category with finite hom-sets exists.**

The obstruction is a pigeonhole. The feedback loop generates an infinite hom-set
`effector ⟶ effector` (the loop and all its powers, distinguished by length); a
faithful functor is injective on hom-sets, so it would inject that infinite set
into a finite one — impossible.

This turns "Joslyn is categorically incomparable to the others by standard means"
(previously stated as folklore) into a theorem: feedback is a genuine boundary of
the finite-shape method, not a gap in effort.
-/

open CategoryTheory Quiver

/-- `nLoop n` : the path `effector ⟶ effector` given by `n` iterations of the
afferent ∘ efferent feedback loop. It has length `2 * n`. -/
def nLoop : ℕ → Quiver.Path (JoslynPosition.effector) (JoslynPosition.effector)
  | 0 => Quiver.Path.nil
  | (n + 1) => ((nLoop n).cons JoslynArrow.efferent).cons JoslynArrow.afferent

/-- The `n`-fold feedback loop has length `2 * n`. -/
theorem nLoop_length (n : ℕ) : (nLoop n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [nLoop, Quiver.Path.length_cons, ih]; omega

/-- Distinct iteration counts give distinct loops (their lengths differ). -/
theorem nLoop_injective : Function.Injective nLoop := by
  intro a b h
  have hlen := congrArg Quiver.Path.length h
  rw [nLoop_length, nLoop_length] at hlen
  omega

/-- The feedback hom-set `effector ⟶ effector` is infinite. -/
instance : Infinite (Quiver.Path (JoslynPosition.effector) (JoslynPosition.effector)) :=
  Infinite.of_injective nLoop nLoop_injective

/-- **Joslyn's feedback shape admits no faithful functor into any category with
finite hom-sets.** The feedback loop makes `effector ⟶ effector` infinite;
faithfulness would inject it into the finite hom-set of the target.

**In `Paths V`, drive hom inference through `Quiver.Path`, never through object
ascription.** `Paths V := V`, and `V`'s own `Quiver` instance shadows the path
category, so `(x : Paths V)` collapses to `x : V` and `x ⟶ x` grabs the raw quiver
(`JoslynArrow`), not `Quiver.Path`. Naming `F.map_injective`'s objects then demands a
bogus `Category V`. The fix: feed an explicitly `Quiver.Path`-typed term to `F.map`
(`fun p : Quiver.Path _ _ => F.map p`) and let unification pin the objects. -/
theorem joslyn_no_faithful_functor
    {C : Type*} [Category C] [∀ X Y : C, Finite (X ⟶ Y)]
    (F : JoslynShape ⥤ C) : ¬ F.Faithful := by
  intro hF
  haveI := hF
  -- Faithfulness injects the (infinite) feedback hom-set `Path effector effector`
  -- into the target's finite hom-set — impossible.
  have hmap : Function.Injective
      (fun p : Quiver.Path (JoslynPosition.effector) JoslynPosition.effector => F.map p) :=
    fun _ _ h => F.map_injective h
  haveI : Finite (Quiver.Path (JoslynPosition.effector) JoslynPosition.effector) :=
    Finite.of_injective _ hmap
  exact not_finite (Quiver.Path (JoslynPosition.effector) JoslynPosition.effector)
