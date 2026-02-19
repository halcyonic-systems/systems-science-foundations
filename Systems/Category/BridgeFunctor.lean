/-
  Systems/Category/BridgeFunctor.lean
  Mobus-Bunge bridge as a functor, bridge factorization (Phase 1, Step 1.4)

  The Mobus→Bunge projection (Bridge.lean) and the Mobus→Rich projection
  (StructureFamily.lean) are functors between the subsystem categories.
  The key categorical result: the bridge factors through the structure
  family as Mobus → Rich → Bunge, and this factorization commutes.

  CATEGORICAL PUNCHLINE (Finding 6):
    bridgeFunctor = embedFunctor ⋙ flattenFunctor

  This says: going from Mobus to Bunge directly (via toBunge) is the same
  as going Mobus → Rich (via toRichBunge, 2-element family) and then
  Rich → Bunge (via flatten). The proof uses `toRichBunge_flatten_eq`
  (StructureFamily.lean:430) which shows flatten({N, G}) = totalRelation.
-/

import Mathlib.CategoryTheory.Category.Preorder
import Systems.Category.FlattenFunctor
import Systems.Category.SubsystemCategory
import Systems.Mobus.Bridge
import Systems.Bunge.StructureFamily

open CategoryTheory

namespace Systems

/-! ## Embed Functor: MobusSys ⥤ RichSys

    The embedding maps a Mobus 8-tuple to a RichConcreteSystem with a
    2-element structure family {internal network, external flows}. -/

/-- toRichBunge preserves the Mobus subsystem ordering.
    If sys₁ is a Mobus subsystem of sys₂, then their rich projections
    stand in the flat subsystem relation. -/
theorem toRichBunge_preserves_subsystem
    {α κ μ π τ η δ : Type*} [ActsOn α]
    {sys₁ sys₂ : MobusSystem α κ μ π τ η δ}
    (hf₁ : FlowInducesAction sys₁.internalNetwork)
    (hg₁ : sys₁.internalNetwork.edges.Nonempty)
    (hf₂ : FlowInducesAction sys₂.internalNetwork)
    (hg₂ : sys₂.internalNetwork.edges.Nonempty)
    (hsub : MobusSubsystem sys₁ sys₂) :
    RichSubsystem_flat (sys₁.toRichBunge hf₁ hg₁) (sys₂.toRichBunge hf₂ hg₂) := by
  refine ⟨hsub.1, hsub.2.1, ?_⟩
  -- Flatten of toRichBunge = totalRelation (by toRichBunge_flatten_eq)
  rw [sys₁.toRichBunge_flatten_eq hf₁ hg₁, sys₂.toRichBunge_flatten_eq hf₂ hg₂]
  exact hsub.2.2

/-! ## Bridge Factorization

    The bridge factors through the structure family:
      toBunge = toRichBunge ⋙ flatten

    At the object level this says:
      sys.toBunge hf hg = (sys.toRichBunge hf hg).toConcreteSystem

    This holds because flatten({internal, external}) = totalRelation
    (by toRichBunge_flatten_eq), and both paths map components → composition
    and environment.objects → environment. -/

/-- The bridge factors: toBunge = toRichBunge followed by flatten.
    This is the categorical content of Finding 6: the Mobus→Bunge passage
    factors through the structure family as Mobus → Rich → Bunge. -/
theorem bridge_factors {α κ μ π τ η δ : Type*} [ActsOn α]
    (sys : MobusSystem α κ μ π τ η δ)
    (hf : FlowInducesAction sys.internalNetwork)
    (hg : sys.internalNetwork.edges.Nonempty) :
    sys.toBunge hf hg = (sys.toRichBunge hf hg).toConcreteSystem := by
  -- Both sides have the same composition and environment.
  -- Structure: LHS is totalRelation, RHS is flatten of {internal, external}.
  -- These are equal by toRichBunge_flatten_eq.
  simp only [MobusSystem.toBunge, RichConcreteSystem.toConcreteSystem,
    MobusSystem.toRichBunge]
  congr 1
  exact (sys.toRichBunge_flatten_eq hf hg).symm

/-- Restating bridge_factors using the flatten functor:
    the object-level factorization holds through flattenFunctor. -/
theorem bridge_factors_functor {α κ μ π τ η δ : Type*} [ActsOn α]
    (sys : MobusSystem α κ μ π τ η δ)
    (hf : FlowInducesAction sys.internalNetwork)
    (hg : sys.internalNetwork.edges.Nonempty) :
    sys.toBunge hf hg = flattenFunctor.obj (sys.toRichBunge hf hg) := by
  rw [flattenFunctor_obj]
  exact bridge_factors sys hf hg

/-! ## Extended Commuting Square

    Combining bridge factorization with the original commuting triangle:

      Mobus ──toBunge──→ Bunge ──toKlir──→ Klir
        |                  ↑
        └─toRichBunge─→ Rich ─flatten─┘

    All paths from Mobus to Klir agree (by triangle_commutes and
    rich_triangle_commutes). The bridge factorization adds the
    intermediate Rich node to the diagram. -/

/-- The extended diagram commutes: Mobus → Rich → Bunge → Klir = Mobus → Klir.
    Combines bridge_factors with the original commuting triangle. -/
theorem extended_diagram_commutes {α κ μ π τ η δ : Type*} [ActsOn α]
    (sys : MobusSystem α κ μ π τ η δ)
    (hf : FlowInducesAction sys.internalNetwork)
    (hg : sys.internalNetwork.edges.Nonempty) :
    (sys.toRichBunge hf hg).toConcreteSystem.toKlir = sys.toKlir := by
  rw [← bridge_factors sys hf hg]
  exact triangle_commutes sys hf hg

end Systems
