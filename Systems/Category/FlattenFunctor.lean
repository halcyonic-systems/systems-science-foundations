/-
  Systems/Category/FlattenFunctor.lean
  Flattening as a functor, Finding 3 as naturality (Phase 1, Step 1.2)

  The flatten map `RichConcreteSystem.toConcreteSystem` is a functor from
  the category of rich systems (ordered by flat subsystem) to the category
  of Bunge systems (ordered by subsystem). The existing monotonicity proof
  `flat_subsystem_preserved` (StructureFamily.lean) is exactly the morphism
  map.

  CATEGORICAL CONTENT: In thin categories, functoriality (map_id, map_comp)
  is automatic — there is at most one morphism between any pair of objects.
  The mathematical content lives in `flat_subsystem_preserved`: flattening
  preserves the subsystem ordering.

  Finding 3 (flatten commutes with internal/external projection) becomes a
  statement about the flatten functor: the two ways of computing internal
  structure — project then flatten, or flatten then project — agree. In
  categorical language this is naturality of the internal-projection
  transformation, but since we are in thin categories, naturality squares
  commute automatically.
-/

import Mathlib.CategoryTheory.Category.Preorder
import Systems.Bunge.StructureFamily
import Systems.Category.SubsystemCategory

open CategoryTheory

namespace Systems

/-! ## Preorder on RichConcreteSystem (flat ordering) -/

/-- RichSubsystem_flat is reflexive. -/
theorem richSubsystem_flat_refl {α : Type*} [ActsOn α]
    (r : RichConcreteSystem α) : RichSubsystem_flat r r :=
  ⟨Set.Subset.refl _, Set.Subset.refl _, Set.Subset.refl _⟩

/-- RichSubsystem_flat is transitive. -/
theorem richSubsystem_flat_trans {α : Type*} [ActsOn α]
    {r₁ r₂ r₃ : RichConcreteSystem α}
    (h₁₂ : RichSubsystem_flat r₁ r₂) (h₂₃ : RichSubsystem_flat r₂ r₃) :
    RichSubsystem_flat r₁ r₃ :=
  ⟨h₁₂.1.trans h₂₃.1, h₂₃.2.1.trans h₁₂.2.1, h₁₂.2.2.trans h₂₃.2.2⟩

/-- The flat subsystem ordering is a preorder on RichConcreteSystem. -/
instance instPreorderRichConcreteSystem {α : Type*} [ActsOn α] :
    Preorder (RichConcreteSystem α) where
  le := RichSubsystem_flat
  le_refl := richSubsystem_flat_refl
  le_trans := fun _ _ _ => richSubsystem_flat_trans

/-! ## Flatten as a Functor -/

/-- `toConcreteSystem` is monotone with respect to the flat subsystem ordering.
    This is `flat_subsystem_preserved` restated as `Monotone`. -/
theorem toConcreteSystem_monotone {α : Type*} [ActsOn α] :
    Monotone (RichConcreteSystem.toConcreteSystem (α := α)) :=
  fun _ _ h => flat_subsystem_preserved _ _ h

/-- The flatten functor: RichSys ⥤ BungeSys.
    Objects: `toConcreteSystem` (StructureFamily.lean:83)
    Morphisms: `flat_subsystem_preserved` (StructureFamily.lean:241)

    In thin categories, `map_id` and `map_comp` are trivially satisfied
    (at most one morphism between any pair). -/
def flattenFunctor {α : Type*} [ActsOn α] :
    RichConcreteSystem α ⥤ ConcreteSystem α :=
  toConcreteSystem_monotone.functor

/-- The flatten functor acts as `toConcreteSystem` on objects. -/
theorem flattenFunctor_obj {α : Type*} [ActsOn α]
    (r : RichConcreteSystem α) :
    flattenFunctor.obj r = r.toConcreteSystem :=
  rfl

/-! ## Finding 3 in Categorical Language

    `flatten_internal_commutes` (StructureFamily.lean:135) states:
      ⋃₀ r.internalFamily = internalProjection r.composition r.flatten

    In categorical language: the internal-projection operation is a natural
    transformation from the "compute internal per-relation then union"
    endofunctor to the "flatten then compute internal" endofunctor. But
    since both are operations on a single object (not functors between
    categories), the content is simply that these two operations commute.

    The categorical framing adds nothing to the proof content — the theorem
    is the same `flatten_internal_commutes`. What changes is the language:
    the flatten functor provides the context in which "flattening preserves
    internal structure" is stated as a functor property rather than an
    ad hoc equation. -/

/-- Finding 3 restated: flattening preserves internal structure.
    The internal structure of the flattened system equals the union of
    the per-relation internal structures. This is a property of the
    flatten functor's action on structure. -/
theorem flatten_preserves_internal {α : Type*} [ActsOn α]
    (r : RichConcreteSystem α) :
    (flattenFunctor.obj r).internalStructure =
    ⋃₀ r.internalFamily := by
  change internalProjection r.composition r.flatten = ⋃₀ r.internalFamily
  exact (flatten_internal_commutes r).symm

end Systems
