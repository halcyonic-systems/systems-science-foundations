/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Types.Basic

/-!
# Rosen's conjugacy is the isomorphism relation of the arrow category

Mapping 008, claim 4. Rosen 1978 §7.10 (*Fundamentals of Measurement and
Representation of Natural Systems*, book pp. 184–186; read from the page images
2026-09-16, scan pages 202–204).

## What the pages say

p. 184: a covariant functor T from the one-arrow category 𝒞_f into 𝒮 "consists
precisely of the diagram T(A) → T(B)"; a morphism in the functor category
𝒟(𝒞_f, 𝒮) is a natural transformation μ making the square A→B over T(A)→T(B)
commute.

p. 185: "Let us say that a map f′: A′ → B′ in 𝒮 is *conjugate* to the map
f: A → B if there is a functor T: 𝒞_f → 𝒮 such that: 1. T(A) = A′; 2. T(B) = B′;
3. T(f) = f′; 4. T is naturally equivalent to the identity functor; i.e., there
exists a natural transformation μ such that the following diagram commutes" —
the square with μ(A): A → A′ on the left, μ(B): B → B′ on the right, f on top,
f′ below. "Naturally equivalent" is fixed on the same page: "the mappings σ are
equivalences in the category 𝒮; i.e., they possess inverses".

p. 186: "Conjugacy imposes an equivalence relation on the set of all mappings in
the category 𝒮", and diagram (7.10.2): f over f′ with vertical α, β, "where α, β
are equivalences".

## The claim, and how it can fail

Mapping 008 claim 4 predicted: Rosen's objects are the kernel's morphisms, and
his modelling relation lives in the arrow category C^→ — but since conjugacy
restricts to natural *equivalences* (his 𝒟_e), it is a **groupoid inside C^→,
not C^→ itself**. Both halves are proved here:

* `conjugate_iff_iso`: conjugacy of f and f′ is exactly an isomorphism
  `Arrow.mk f ≅ Arrow.mk f′` in Mathlib's arrow category. So the relation Rosen
  defines is the isomorphism relation of C^→, and its witnesses (the squares
  with invertible legs) are the maximal subgroupoid of C^→.
* `conjugate_equivalence`: Rosen's p. 186 sentence, derived from the iso.
* `square_not_conjugate`: a morphism of C^→ that is NOT a conjugacy — a commuting
  square in `Type` whose left leg is not invertible. So the groupoid is proper:
  C^→ has morphisms Rosen's relation does not see.

## Arrow direction convention

Squares are read as on p. 185: top f: A → B, bottom f′: A′ → B′, left
α: A → A′, right β: B → B′, commuting as β ∘ f = f′ ∘ α. In Lean's
diagrammatic order that is `f ≫ β.hom = α.hom ≫ f′`. Mathlib's `Arrow.w` states
the same square as `sq.left ≫ g.hom = f.hom ≫ sq.right`.
-/

open CategoryTheory

namespace Systems.Rosen

variable {C : Type*} [Category C]

/-- Rosen's conjugacy (p. 185, diagram 7.10.2): a commuting square whose
vertical legs are equivalences. -/
def Conjugate {A B A' B' : C} (f : A ⟶ B) (f' : A' ⟶ B') : Prop :=
  ∃ (α : A ≅ A') (β : B ≅ B'), f ≫ β.hom = α.hom ≫ f'

/-- Conjugacy is isomorphism in the arrow category. -/
theorem conjugate_iff_iso {A B A' B' : C} (f : A ⟶ B) (f' : A' ⟶ B') :
    Conjugate f f' ↔ Nonempty (Arrow.mk f ≅ Arrow.mk f') := by
  constructor
  · rintro ⟨α, β, w⟩
    exact ⟨Arrow.isoMk' f f' α β w.symm⟩
  · rintro ⟨e⟩
    refine ⟨Arrow.leftFunc.mapIso e, Arrow.rightFunc.mapIso e, ?_⟩
    exact (Arrow.w e.hom).symm

/-- "Conjugacy imposes an equivalence relation on the set of all mappings in
the category" (p. 186) — on arrows as objects of C^→. -/
theorem conjugate_refl {A B : C} (f : A ⟶ B) : Conjugate f f :=
  (conjugate_iff_iso f f).2 ⟨Iso.refl _⟩

theorem conjugate_symm {A B A' B' : C} {f : A ⟶ B} {f' : A' ⟶ B'}
    (h : Conjugate f f') : Conjugate f' f :=
  (conjugate_iff_iso f' f).2 ⟨((conjugate_iff_iso f f').1 h).some.symm⟩

theorem conjugate_trans {A B A' B' A'' B'' : C}
    {f : A ⟶ B} {f' : A' ⟶ B'} {f'' : A'' ⟶ B''}
    (h₁ : Conjugate f f') (h₂ : Conjugate f' f'') : Conjugate f f'' :=
  (conjugate_iff_iso f f'').2
    ⟨((conjugate_iff_iso f f').1 h₁).some ≪≫ ((conjugate_iff_iso f' f'').1 h₂).some⟩

/-- The relation as a `Setoid`-shaped statement, for the record. -/
theorem conjugate_equivalence :
    Equivalence (fun (x y : Arrow C) => Conjugate x.hom y.hom) :=
  ⟨fun x => conjugate_refl x.hom, conjugate_symm, conjugate_trans⟩

/-! ## The groupoid is proper

A commuting square with a non-invertible leg is a morphism of C^→ (Mathlib
accepts it) but not a conjugacy. In `Type`: `Bool → Unit` over `Unit → Unit`,
left leg the collapse `Bool → Unit`. -/

/-- The collapse `Bool → Unit` as a morphism of `Type`. -/
def collapse : (Bool : Type) ⟶ Unit := fun _ => ()

/-- The square: top the collapse, bottom `𝟙 Unit`, left leg the collapse. A
morphism of the arrow category with a non-invertible leg. -/
def collapseSquare : Arrow.mk collapse ⟶ Arrow.mk (𝟙 Unit) where
  left := collapse
  right := 𝟙 Unit
  w := rfl

/-- It is not a conjugacy: no isomorphism `Bool ≅ Unit` exists in `Type`. -/
theorem square_not_conjugate : ¬ Conjugate collapse (𝟙 Unit) := by
  rintro ⟨α, -, -⟩
  -- `α.hom true` and `α.hom false` are definitionally equal in `Unit`.
  have ht : α.inv (α.hom true) = true := congrFun α.hom_inv_id true
  have hf : α.inv (α.hom false) = false := congrFun α.hom_inv_id false
  exact absurd (ht.symm.trans hf) (by decide)

end Systems.Rosen
