/-
  Systems/Category/OrderingTriangle.lean
  Three subsystem orderings as a functor triangle (Phase 1, Step 1.3)

  StructureFamily.lean defines three subsystem orderings on RichConcreteSystem:
    (a) flat:       flatten(F₁) ⊆ flatten(F₂)
    (b) refinement: ∀ R₁ ∈ F₁, ∃ R₂ ∈ F₂, R₁ ⊆ R₂
    (c) family:     F₁ ⊆ F₂

  These form a strict hierarchy (Finding 8):
    family ⟹ refinement ⟹ flat  (strict in both cases)

  Categorically, each ordering gives a thin category on RichConcreteSystem.
  Since Lean allows only one Preorder instance per type, we use structure
  wrappers. The implications become forgetful functors:

    FamilyOrd ─→ RefinementOrd ─→ FlatOrd

  All functors are faithful (automatic for thin categories) but NOT full.
  The non-fullness is witnessed by concrete counterexamples on Fin 2.
-/

import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Systems.Bunge.StructureFamily
import Systems.Category.SubsystemCategory

open CategoryTheory

namespace Systems

/-! ## Wrapper Types

    Structure wrappers ensure Lean selects the correct Preorder instance
    for each ordering. All three carry the same data (`RichConcreteSystem α`)
    but equip it with a different `≤`. -/

/-- RichConcreteSystem with the flat subsystem ordering. -/
structure FlatOrd (α : Type*) [ActsOn α] where
  /-- The underlying rich concrete system. -/
  val : RichConcreteSystem α

/-- RichConcreteSystem with the refinement subsystem ordering. -/
structure RefinementOrd (α : Type*) [ActsOn α] where
  /-- The underlying rich concrete system. -/
  val : RichConcreteSystem α

/-- RichConcreteSystem with the family subsystem ordering. -/
structure FamilyOrd (α : Type*) [ActsOn α] where
  /-- The underlying rich concrete system. -/
  val : RichConcreteSystem α

/-! ## Preorder Instances -/

/-- Flat subsystem ordering on FlatOrd. -/
instance instPreorderFlatOrd {α : Type*} [ActsOn α] : Preorder (FlatOrd α) where
  le r₁ r₂ := RichSubsystem_flat r₁.val r₂.val
  le_refl _ := ⟨Set.Subset.refl _, Set.Subset.refl _, Set.Subset.refl _⟩
  le_trans _ _ _ h₁₂ h₂₃ :=
    ⟨h₁₂.1.trans h₂₃.1, h₂₃.2.1.trans h₁₂.2.1, h₁₂.2.2.trans h₂₃.2.2⟩

/-- Refinement subsystem ordering: ∀ R₁ ∈ F₁, ∃ R₂ ∈ F₂, R₁ ⊆ R₂. -/
instance instPreorderRefinementOrd {α : Type*} [ActsOn α] :
    Preorder (RefinementOrd α) where
  le r₁ r₂ := RichSubsystem_refinement r₁.val r₂.val
  le_refl _ :=
    ⟨Set.Subset.refl _, Set.Subset.refl _,
     fun R hR => ⟨R, hR, Set.Subset.refl _⟩⟩
  le_trans _ _ _ h₁₂ h₂₃ :=
    ⟨h₁₂.1.trans h₂₃.1, h₂₃.2.1.trans h₁₂.2.1,
     fun R₁ hR₁ => by
       obtain ⟨R₂, hR₂, h₁₂'⟩ := h₁₂.2.2 R₁ hR₁
       obtain ⟨R₃, hR₃, h₂₃'⟩ := h₂₃.2.2 R₂ hR₂
       exact ⟨R₃, hR₃, h₁₂'.trans h₂₃'⟩⟩

/-- Family subsystem ordering: F₁ ⊆ F₂. -/
instance instPreorderFamilyOrd {α : Type*} [ActsOn α] : Preorder (FamilyOrd α) where
  le r₁ r₂ := RichSubsystem_family r₁.val r₂.val
  le_refl _ := ⟨Set.Subset.refl _, Set.Subset.refl _, Set.Subset.refl _⟩
  le_trans _ _ _ h₁₂ h₂₃ :=
    ⟨h₁₂.1.trans h₂₃.1, h₂₃.2.1.trans h₁₂.2.1, h₁₂.2.2.trans h₂₃.2.2⟩

/-! ## Forgetful Functors -/

/-- Family → Refinement: wrapping is monotone. -/
private theorem familyToRefinement_monotone {α : Type*} [ActsOn α] :
    Monotone (fun r : FamilyOrd α => RefinementOrd.mk r.val) :=
  fun _ _ h => family_implies_refinement _ _ h

/-- Refinement → Flat: wrapping is monotone. -/
private theorem refinementToFlat_monotone {α : Type*} [ActsOn α] :
    Monotone (fun r : RefinementOrd α => FlatOrd.mk r.val) :=
  fun _ _ h => refinement_implies_flat _ _ h

/-- Forgetful functor: FamilyOrd ⥤ RefinementOrd.
    Identity on underlying data, relabels ordering from family to refinement. -/
def forgetFamily {α : Type*} [ActsOn α] : FamilyOrd α ⥤ RefinementOrd α :=
  familyToRefinement_monotone.functor

/-- Forgetful functor: RefinementOrd ⥤ FlatOrd.
    Identity on underlying data, relabels ordering from refinement to flat. -/
def forgetRefinement {α : Type*} [ActsOn α] : RefinementOrd α ⥤ FlatOrd α :=
  refinementToFlat_monotone.functor

/-! ## Faithfulness (automatic for thin categories) -/

/-- forgetFamily is faithful (at most one morphism between any pair). -/
instance instFaithfulForgetFamily {α : Type*} [ActsOn α] :
    (forgetFamily (α := α)).Faithful where
  map_injective := fun {_ _} {_ _} _ => Subsingleton.elim _ _

/-- forgetRefinement is faithful (at most one morphism between any pair). -/
instance instFaithfulForgetRefinement {α : Type*} [ActsOn α] :
    (forgetRefinement (α := α)).Faithful where
  map_injective := fun {_ _} {_ _} _ => Subsingleton.elim _ _

/-! ## Non-Fullness: Concrete Counterexamples

    To show the forgetful functors are NOT full, we construct explicit
    RichConcreteSystem values where a weaker ordering holds but a stronger
    one does not. We use Fin 2 with a minimal ActsOn instance. -/

/-- Minimal ActsOn instance on Fin 2: 0 acts on 1, nothing else. -/
instance instActsOnFin2 : ActsOn (Fin 2) where
  actsOn a b := a = 0 ∧ b = 1

/-- A RichConcreteSystem on Fin 2 with a single 2-pair relation.
    composition = {0, 1}, environment = ∅, family = {{(0,1), (1,0)}}. -/
private def sys_merged : RichConcreteSystem (Fin 2) where
  composition := {0, 1}
  environment := ∅
  structureFamily := {{(0, 1), (1, 0)}}
  disjoint := by ext x; simp
  family_on := by
    intro R hR p hp
    simp only [Set.mem_singleton_iff] at hR; subst hR
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    simp only [Set.mem_union, Set.mem_empty_iff_false, or_false]
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Set.mem_insert 0 _, Set.mem_insert_of_mem 0 rfl⟩
    · exact ⟨Set.mem_insert_of_mem 0 rfl, Set.mem_insert 0 _⟩
  bondage_nonempty := by
    refine ⟨0, Set.mem_insert 0 _, 1, Set.mem_insert_of_mem 0 rfl, by decide, ?_⟩
    exact Or.inl ⟨rfl, rfl⟩

/-- A RichConcreteSystem on Fin 2 with two singleton relations.
    composition = {0, 1}, environment = ∅, family = {{(0,1)}, {(1,0)}}. -/
private def sys_split : RichConcreteSystem (Fin 2) where
  composition := {0, 1}
  environment := ∅
  structureFamily := {{(0, 1)}, {(1, 0)}}
  disjoint := by ext x; simp
  family_on := by
    intro R hR p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hR
    simp only [Set.mem_union, Set.mem_empty_iff_false, or_false]
    rcases hR with rfl | rfl
    · simp only [Set.mem_singleton_iff] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨Set.mem_insert 0 _, Set.mem_insert_of_mem 0 rfl⟩
    · simp only [Set.mem_singleton_iff] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨Set.mem_insert_of_mem 0 rfl, Set.mem_insert 0 _⟩
  bondage_nonempty := by
    refine ⟨0, Set.mem_insert 0 _, 1, Set.mem_insert_of_mem 0 rfl, by decide, ?_⟩
    exact Or.inl ⟨rfl, rfl⟩

/-- sys_merged ≤_flat sys_split: both flatten to {(0,1), (1,0)}. -/
private theorem flat_holds : (⟨sys_merged⟩ : FlatOrd (Fin 2)) ≤ ⟨sys_split⟩ := by
  refine ⟨Set.Subset.refl _, Set.Subset.refl _, ?_⟩
  intro p hp
  simp only [sys_merged, sys_split, RichConcreteSystem.flatten, Set.mem_sUnion,
    Set.mem_singleton_iff, Set.mem_insert_iff] at hp ⊢
  obtain ⟨S, rfl, hp⟩ := hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact ⟨{(0, 1)}, Or.inl rfl, rfl⟩
  · exact ⟨{(1, 0)}, Or.inr rfl, rfl⟩

/-- sys_merged is NOT a refinement subsystem of sys_split.
    The single relation {(0,1),(1,0)} in sys_merged's family cannot be
    contained in any single relation of sys_split's family (each has only
    one pair). -/
private theorem refinement_fails :
    ¬ ((⟨sys_merged⟩ : RefinementOrd (Fin 2)) ≤ ⟨sys_split⟩) := by
  intro ⟨_, _, href⟩
  have h := href {(0, 1), (1, 0)} (Set.mem_singleton _)
  obtain ⟨R₂, hR₂, hle⟩ := h
  simp only [sys_split, Set.mem_insert_iff, Set.mem_singleton_iff] at hR₂
  rcases hR₂ with rfl | rfl
  · have h10 := hle (Set.mem_insert_of_mem _ rfl)
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h10
    exact absurd h10.2 (by decide)
  · have h01 := hle (Set.mem_insert _ _)
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h01
    exact absurd h01.1 (by decide)

/-- forgetRefinement is NOT full.
    Witness: sys_merged ≤_flat sys_split but ¬ (sys_merged ≤_ref sys_split).
    There is a morphism in FlatOrd with no preimage in RefinementOrd. -/
theorem not_full_forgetRefinement :
    ¬ (forgetRefinement (α := Fin 2)).Full := by
  intro ⟨hsurj⟩
  -- A morphism in FlatOrd from flat_holds
  have hmor : forgetRefinement.obj ⟨sys_merged⟩ ⟶ forgetRefinement.obj ⟨sys_split⟩ :=
    homOfLE flat_holds
  -- Surjectivity gives a preimage in RefinementOrd
  obtain ⟨g, _⟩ := hsurj hmor
  -- leOfHom extracts the refinement ordering, contradicting refinement_fails
  exact refinement_fails (leOfHom g)

/-! ## Non-fullness of forgetFamily -/

/-- A system with one small relation: family = {{(0,1)}}. -/
private def sys_small : RichConcreteSystem (Fin 2) where
  composition := {0, 1}
  environment := ∅
  structureFamily := {{(0, 1)}}
  disjoint := by ext x; simp
  family_on := by
    intro R hR p hp
    simp only [Set.mem_singleton_iff] at hR; subst hR
    simp only [Set.mem_singleton_iff] at hp
    obtain ⟨rfl, rfl⟩ := hp
    simp only [Set.mem_union, Set.mem_empty_iff_false, or_false]
    exact ⟨Set.mem_insert 0 _, Set.mem_insert_of_mem 0 rfl⟩
  bondage_nonempty := by
    refine ⟨0, Set.mem_insert 0 _, 1, Set.mem_insert_of_mem 0 rfl, by decide, ?_⟩
    exact Or.inl ⟨rfl, rfl⟩

/-- sys_small ≤_ref sys_merged: {(0,1)} ⊆ {(0,1),(1,0)}. -/
private theorem refinement_small_merged :
    (⟨sys_small⟩ : RefinementOrd (Fin 2)) ≤ ⟨sys_merged⟩ := by
  refine ⟨Set.Subset.refl _, Set.Subset.refl _, ?_⟩
  intro R₁ hR₁
  simp only [sys_small, Set.mem_singleton_iff] at hR₁; subst hR₁
  exact ⟨{(0, 1), (1, 0)}, Set.mem_singleton _,
    Set.singleton_subset_iff.mpr (Set.mem_insert _ _)⟩

/-- sys_small is NOT a family subsystem of sys_merged.
    {(0,1)} ∉ {{(0,1),(1,0)}} — the singleton is not the same set as the pair. -/
private theorem family_small_merged_fails :
    ¬ ((⟨sys_small⟩ : FamilyOrd (Fin 2)) ≤ ⟨sys_merged⟩) := by
  intro ⟨_, _, hfam⟩
  have h := hfam (Set.mem_singleton _)
  simp only [sys_merged, Set.mem_singleton_iff] at h
  have h10 : ((1 : Fin 2), (0 : Fin 2)) ∈ ({(0, 1)} : Set (Fin 2 × Fin 2)) := by
    rw [h]; exact Set.mem_insert_of_mem _ rfl
  simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h10
  exact absurd h10.1 (by decide)

/-- forgetFamily is NOT full.
    Witness: sys_small ≤_ref sys_merged but ¬ (sys_small ≤_fam sys_merged).
    There is a morphism in RefinementOrd with no preimage in FamilyOrd. -/
theorem not_full_forgetFamily :
    ¬ (forgetFamily (α := Fin 2)).Full := by
  intro ⟨hsurj⟩
  have hmor : forgetFamily.obj ⟨sys_small⟩ ⟶ forgetFamily.obj ⟨sys_merged⟩ :=
    homOfLE refinement_small_merged
  obtain ⟨g, _⟩ := hsurj hmor
  exact family_small_merged_fails (leOfHom g)

end Systems
