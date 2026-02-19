/-
  Systems/Category/SubsystemCategory.lean
  Subsystem orderings as thin categories (Phase 1, Step 1.1)

  The subsystem relations on ConcreteSystem and MobusSystem form preorders.
  Mathlib's `Preorder.smallCategory` automatically promotes these to thin
  categories: objects are systems, a morphism σ₁ ⟶ σ₂ exists iff σ₁ ≤ σ₂
  (i.e., σ₁ is a subsystem of σ₂).

  CATEGORICAL CONTENT: Every preorder is a thin category — at most one
  morphism between any two objects. The Bunge and Mobus subsystem orderings
  are preorders, giving two thin categories:
    BungeSys := (ConcreteSystem α, Subsystem)
    MobusSys := (MobusSystem α κ μ π τ η δ, MobusSubsystem)

  DESIGN: We use Preorder (not PartialOrder) because although antisymmetry
  holds on the CES triple fields, ConcreteSystem carries proof fields whose
  propositional equality requires proof irrelevance. Preorder suffices for
  the thin category structure.
-/

import Mathlib.CategoryTheory.Category.Preorder
import Systems.Core.System
import Systems.Mobus.Bridge

namespace Systems

/-! ## Bunge Subsystem Preorder -/

/-- The Bunge subsystem relation is a preorder on ConcreteSystem.
    Reflexivity: `subsystem_refl` (System.lean).
    Transitivity: `subsystem_trans` (System.lean).

    Mathlib's `Preorder.smallCategory` then gives a thin category:
    objects = concrete systems, a morphism σ₁ ⟶ σ₂ exists iff
    Subsystem σ₁ σ₂ (i.e., C₁ ⊆ C₂, E₂ ⊆ E₁, S₁ ⊆ S₂). -/
instance instPreorderConcreteSystem {α : Type*} [ActsOn α] :
    Preorder (ConcreteSystem α) where
  le := Subsystem
  le_refl := subsystem_refl
  le_trans := fun _ _ _ h₁₂ h₂₃ => subsystem_trans h₁₂ h₂₃

/-! ## Mobus Subsystem Preorder

    MobusSubsystem (Bridge.lean) has the same three-component structure as
    Bunge's Subsystem. Reflexivity and transitivity are component-wise
    (Set.Subset is a preorder on each component). These are proved here
    because Bridge.lean predates the categorical layer. -/

/-- MobusSubsystem is reflexive. -/
theorem mobusSubsystem_refl {α κ μ π τ η δ : Type*}
    (sys : MobusSystem α κ μ π τ η δ) :
    MobusSubsystem sys sys :=
  ⟨Set.Subset.refl _, Set.Subset.refl _, Set.Subset.refl _⟩

/-- MobusSubsystem is transitive. -/
theorem mobusSubsystem_trans {α κ μ π τ η δ : Type*}
    {sys₁ sys₂ sys₃ : MobusSystem α κ μ π τ η δ}
    (h₁₂ : MobusSubsystem sys₁ sys₂) (h₂₃ : MobusSubsystem sys₂ sys₃) :
    MobusSubsystem sys₁ sys₃ :=
  ⟨h₁₂.1.trans h₂₃.1, h₂₃.2.1.trans h₁₂.2.1, h₁₂.2.2.trans h₂₃.2.2⟩

/-- The Mobus subsystem relation is a preorder on MobusSystem.
    Reflexivity and transitivity are component-wise (⊆ is a preorder). -/
instance instPreorderMobusSystem {α κ μ π τ η δ : Type*} :
    Preorder (MobusSystem α κ μ π τ η δ) where
  le := MobusSubsystem
  le_refl := mobusSubsystem_refl
  le_trans := fun _ _ _ h₁₂ h₂₃ => mobusSubsystem_trans h₁₂ h₂₃

/-! ## Bridge is monotone

    toBunge preserves the subsystem ordering — this is `toBunge_preserves_subsystem`
    (Bridge.lean). Restated here as a `Monotone` lemma for use with
    `Monotone.functor` in BridgeFunctor.lean. -/

/-- The Mobus→Bunge projection is monotone: subsystem ordering is preserved. -/
theorem toBunge_monotone {α κ μ π τ η δ : Type*} [ActsOn α]
    (hf : (sys : MobusSystem α κ μ π τ η δ) → FlowInducesAction sys.internalNetwork)
    (hg : (sys : MobusSystem α κ μ π τ η δ) → sys.internalNetwork.edges.Nonempty) :
    Monotone (fun sys : MobusSystem α κ μ π τ η δ => sys.toBunge (hf sys) (hg sys)) :=
  fun _ _ hsub => ⟨hsub.1, hsub.2.1, hsub.2.2⟩

end Systems
