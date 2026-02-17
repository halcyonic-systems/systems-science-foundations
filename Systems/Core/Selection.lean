/-
  Systems/Core/Selection.lean
  Environmental selection, selective action, and composition

  Formalizes Bunge, Treatise on Basic Philosophy Vol. 4, §3.3:
  - Selective action i_E : S → A_E (Def 1.15)
  - Adapted and eliminated sets (Def 1.15(ii))
  - Universal selection postulate (Post 1.6)
  - Selection composition theorem (Thm 1.2)

  SHOWCASE THEOREM #2: Selection composition — i_{EE'} = i_{E'} ∘ i_E

  DESIGN: We use Set-based definitions rather than Finset to keep imports
  minimal and avoid decidability requirements. Selection pressure (which
  needs cardinality) is deferred to Phase 2 where Fintype instances are available.
-/

import Systems.Core.System

namespace Systems

/-! ## Selective Action (Bunge Def 1.15) -/

/-- A selective action represents the filtering of a population S by
    an environment, yielding an adapted set A_E ⊆ S.
    Bunge Def 1.15(i): i_E : S → A_E is the inclusion function from S
    into A_E, where A_E ⊆ S.

    The environment exerts selective action on S iff, during the next
    time interval, only the members of A_E remain in S. -/
structure SelectiveAction (α : Type*) where
  /-- The original population of systems -/
  population : Set α
  /-- The adapted (surviving) subset -/
  adapted : Set α
  /-- Adapted is a subset of population -/
  adapted_sub : adapted ⊆ population

/-- The eliminated set: systems removed by selection.
    Bunge Def 1.15(ii): Ā_E = S - A_E. -/
def SelectiveAction.eliminated {α : Type*}
    (sel : SelectiveAction α) : Set α :=
  sel.population \ sel.adapted

/-- The population is partitioned into adapted and eliminated.
    adapted ∪ eliminated = population. -/
theorem SelectiveAction.partition {α : Type*}
    (sel : SelectiveAction α) :
    sel.adapted ∪ sel.eliminated = sel.population := by
  ext x
  simp [SelectiveAction.eliminated, Set.mem_diff]
  constructor
  · rintro (h | ⟨hp, _⟩) <;> [exact sel.adapted_sub h; exact hp]
  · intro hp
    by_cases ha : x ∈ sel.adapted
    · exact Or.inl ha
    · exact Or.inr ⟨hp, ha⟩

/-- Adapted and eliminated are disjoint. -/
theorem SelectiveAction.adapted_eliminated_disjoint {α : Type*}
    (sel : SelectiveAction α) :
    sel.adapted ∩ sel.eliminated = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, SelectiveAction.eliminated, Set.mem_diff,
    Set.mem_empty_iff_false, iff_false, not_and, not_not]
  exact fun h _ => h

/-! ## Selection Composition (Bunge Thm 1.2) -/

/-- Compose two consecutive selective actions.
    Bunge Thm 1.2: If E and E' are two different consecutive environments,
    the resulting selective action is i_{EE'} = i_{E'} ∘ i_E.

    The second environment acts on the survivors of the first. -/
def SelectiveAction.compose {α : Type*}
    (sel₁ : SelectiveAction α) (sel₂ : SelectiveAction α)
    (h : sel₂.population = sel₁.adapted) : SelectiveAction α where
  population := sel₁.population
  adapted := sel₂.adapted
  adapted_sub := by
    intro x hx
    have h₂ := sel₂.adapted_sub hx
    rw [h] at h₂
    exact sel₁.adapted_sub h₂

/-- The adapted set of a composed selection is a subset of the first
    environment's adapted set.
    Consequence of Thm 1.2: A_{EE'} ⊆ A_E. -/
theorem SelectiveAction.compose_adapted_sub {α : Type*}
    (sel₁ : SelectiveAction α) (sel₂ : SelectiveAction α)
    (h : sel₂.population = sel₁.adapted) :
    (sel₁.compose sel₂ h).adapted ⊆ sel₁.adapted := by
  intro x hx
  have h₂ := sel₂.adapted_sub hx
  rw [h] at h₂
  exact h₂

/-- The composed adapted set is exactly the second selection's adapted set.
    This is the core of Thm 1.2: composition of inclusion maps. -/
theorem SelectiveAction.compose_adapted_eq {α : Type*}
    (sel₁ : SelectiveAction α) (sel₂ : SelectiveAction α)
    (h : sel₂.population = sel₁.adapted) :
    (sel₁.compose sel₂ h).adapted = sel₂.adapted :=
  rfl

/-- Selection composition is associative.
    Consequence of Thm 1.2: the adapted set of a triple composition
    equals the adapted set of the third selection. -/
theorem SelectiveAction.compose_assoc_adapted {α : Type*}
    (s₁ s₂ s₃ : SelectiveAction α)
    (h₁₂ : s₂.population = s₁.adapted)
    (h₂₃ : s₃.population = s₂.adapted) :
    ((s₁.compose s₂ h₁₂).compose s₃
      (by rw [compose_adapted_eq]; exact h₂₃)).adapted = s₃.adapted :=
  rfl

/-! ## Postulate 1.6: Universal Selection -/

/-- Bunge Postulate 1.6: All systems are subject to environmental selection.
    For every set S of any kind K and every environment E common to the
    members of S, there is a selective action i_E : S → A_E with A_E ⊂ S.

    We express this as: the adapted set is always a proper subset. -/
def UniversalSelection (α : Type*) : Prop :=
  ∀ (sel : SelectiveAction α),
    sel.population.Nonempty → sel.adapted ⊂ sel.population

end Systems
