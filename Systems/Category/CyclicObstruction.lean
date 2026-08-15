/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.Data.Finite.Set

/-!
# Cyclicity is a boundary of the finite-shape method (shared obstruction)

The landscape has two cyclic shapes — Joslyn (feedback through observation,
`effector ⇄ controlled`) and Spivak (feedback through value,
`parameter ⇄ potential`) — and both are unreachable by the comparison
apparatus that places the DAG-shaped traditions. This file proves the
obstruction ONCE, parameterized over the loop (issue #21 route (a)):

**any free category `Paths V` whose quiver carries a positive-length
self-returning path admits no faithful functor into a category with finite
hom-sets.**

The pigeonhole: the loop's powers `cyclePow loop n` are distinguished by
length (`n * loop.length`), so the hom-set `v ⟶ v` is infinite; a faithful
functor is injective on hom-sets and would inject that infinite set into a
finite one.

`JoslynIncomparability.lean` and `SpivakIncomparability.lean` instantiate
this for their loops. Any future cyclic shape gets its boundary theorem in
two lines: exhibit the loop, cite `paths_no_faithful_functor_of_cycle`.
-/

open CategoryTheory Quiver

variable {V : Type*} [Quiver V] {v : V}

/-- `cyclePow loop n` : the `n`-fold composite of a self-returning path with
itself — the `n`-th power of the loop. -/
def cyclePow (loop : Quiver.Path v v) : ℕ → Quiver.Path v v
  | 0 => Quiver.Path.nil
  | (n + 1) => (cyclePow loop n).comp loop

/-- The `n`-th power of a loop has length `n * loop.length`. -/
theorem cyclePow_length (loop : Quiver.Path v v) (n : ℕ) :
    (cyclePow loop n).length = n * loop.length := by
  induction n with
  | zero => simp [cyclePow]
  | succ k ih => simp only [cyclePow, Quiver.Path.length_comp, ih, Nat.succ_mul]

/-- Distinct powers of a positive-length loop are distinct paths (their
lengths differ). -/
theorem cyclePow_injective (loop : Quiver.Path v v) (hlen : loop.length ≠ 0) :
    Function.Injective (cyclePow loop) := by
  intro a b h
  have := congrArg Quiver.Path.length h
  rw [cyclePow_length, cyclePow_length] at this
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hlen) this

/-- A positive-length self-returning path makes the hom-set `v ⟶ v` of the
free category infinite. -/
theorem infinite_path_of_cycle (loop : Quiver.Path v v) (hlen : loop.length ≠ 0) :
    Infinite (Quiver.Path v v) :=
  Infinite.of_injective (cyclePow loop) (cyclePow_injective loop hlen)

/-- **A `Paths` category with a positive-length self-returning cycle admits no
faithful functor into any category with finite hom-sets.** The cycle's powers
make `v ⟶ v` infinite; faithfulness would inject it into the finite hom-set
of the target.

**In `Paths V`, drive hom inference through `Quiver.Path`, never through
object ascription** (`Paths V := V` lets `V`'s own `Quiver` instance shadow
the path category; see `JoslynIncomparability.lean`'s engineering note). -/
theorem paths_no_faithful_functor_of_cycle
    (loop : Quiver.Path v v) (hlen : loop.length ≠ 0)
    {C : Type*} [Category C] [∀ X Y : C, Finite (X ⟶ Y)]
    (F : Paths V ⥤ C) : ¬ F.Faithful := by
  intro hF
  haveI := hF
  haveI : Infinite (Quiver.Path v v) := infinite_path_of_cycle loop hlen
  have hmap : Function.Injective (fun p : Quiver.Path v v => F.map p) :=
    fun _ _ h => F.map_injective h
  haveI : Finite (Quiver.Path v v) := Finite.of_injective _ hmap
  exact not_finite (Quiver.Path v v)
