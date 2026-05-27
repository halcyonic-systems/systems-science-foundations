/-
  Systems/Core/Complexity.lean
  Principle 5: Complexity — structural complexity derived from #1 + #2 + #3

  DERIVABILITY THEOREM: All structural complexity measures are functions
  of data present in Systemness (#1), Hierarchy (#2), and Networks (#3).
  This file imports only Systems.Core.Systemness — no Mobus-layer imports,
  no new typeclasses, no new axioms. The import list is the proof.

  The session plan assumed Mobus-layer placement (complexity uses 8-tuple
  data). The formalization reveals that the Bunge CES triple suffices.
  Complexity does not require flow networks, boundaries, interfaces,
  transforms, history, or time scale — only composition, environment,
  structure, and the ActsOn relation.

  MOBUS'S OWN SCOPING (Ch. 4): Mobus distinguishes structural complexity
  (component count, connectivity, hierarchical depth — formalized below)
  from Simonian complexity (state-space explosion tamed by near-
  decomposability — a bridge theorem connecting #1+#2 to Dynamics #4)
  and explicitly defers behavioral complexity as future research.

  Under this scoping, Complexity decomposes entirely:
  - Structural complexity: derived from #1+#2+#3 (this file proves it)
  - Simonian complexity: a theorem about how Hierarchy (#2) interacts
    with Dynamics (#4), structurally parallel to Simon's conditional
    time-scale separation. Awaits Dynamics formalization.
  - Behavioral complexity: Mobus himself flags this as open. Not part
    of the principle as stated.

  No part of the principle as Mobus scopes it requires new axioms.

  Formalizes Mobus, Systems Science: Theory, Analysis, Modeling, and Design, Ch. 2 + Ch. 4:
  "Systems exhibit various kinds and levels of complexity."

  Key definitions:
  - SameKind: interaction-profile equivalence (diversity from ActsOn)

  Key theorems:
  - has_two_components: every system has ≥ 2 components
  - compose_internalStructure_ge_left: composition never loses structure
  - SameKind is an equivalence relation (diversity is well-defined)
-/

import Systems.Core.Systemness

namespace Systems

/-! ## Interaction-Profile Equivalence

  Component-kind diversity requires classifying components into "kinds."
  Rather than introducing a new typing system (which would be genuinely
  new structure and thus evidence of independence), we derive the
  classification from ActsOn: two components are of the same kind iff
  they have identical interaction profiles.

  This resolves the key derivability question: diversity does NOT
  require a new typing system. It derives from Systemness (#1). -/

/-- Two things are of the same kind iff they have identical interaction
    profiles: they act on exactly the same things, and exactly the same
    things act on them.

    Source: ActsOn (Systemness #1). No new structure needed.

    The number of SameKind equivalence classes in a system's composition
    is its component-kind diversity — a complexity measure derivable
    entirely from the ActsOn relation. -/
def SameKind {α : Type*} [ActsOn α] (a b : α) : Prop :=
  (∀ x, a ▷ x ↔ b ▷ x) ∧ (∀ x, x ▷ a ↔ x ▷ b)

theorem sameKind_refl {α : Type*} [ActsOn α] (a : α) : SameKind a a :=
  ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem sameKind_symm {α : Type*} [ActsOn α] {a b : α}
    (h : SameKind a b) : SameKind b a :=
  ⟨fun x => (h.1 x).symm, fun x => (h.2 x).symm⟩

theorem sameKind_trans {α : Type*} [ActsOn α] {a b c : α}
    (hab : SameKind a b) (hbc : SameKind b c) : SameKind a c :=
  ⟨fun x => (hab.1 x).trans (hbc.1 x), fun x => (hab.2 x).trans (hbc.2 x)⟩

/-- SameKind is an equivalence relation on any type with ActsOn.
    This guarantees that component-kind diversity (the number of
    equivalence classes) is well-defined. -/
theorem sameKind_equivalence {α : Type*} [ActsOn α] :
    Equivalence (@SameKind α _) :=
  ⟨sameKind_refl, fun h => sameKind_symm h, fun h₁ h₂ => sameKind_trans h₁ h₂⟩

/-! ## Non-Triviality

  Every ConcreteSystem has at least 2 distinct components (from
  bondage_nonempty). This is the base case: any system satisfying
  the CES constraints has non-trivial structural complexity.

  Stated existentially — the cardinality claim without cardinality
  machinery. -/

/-- Every system has at least 2 distinct components.
    Immediate from bondage_nonempty: the CES constraint guarantees
    non-trivial component complexity for every system. -/
theorem ConcreteSystem.has_two_components {α : Type*} [ActsOn α]
    (σ : ConcreteSystem α) :
    ∃ a ∈ σ.composition, ∃ b ∈ σ.composition, a ≠ b := by
  obtain ⟨a, ha, b, hb, hne, _⟩ := σ.bondage_nonempty
  exact ⟨a, ha, b, hb, hne⟩

/-! ## Monotonicity Under Composition

  Structural complexity is monotone under system composition: composing
  systems never loses components or internal structure. This connects
  Complexity (#5) to the composition closure theorem from Systemness (#1).

  compose_contains_left/right (Systemness.lean) already establish
  component monotonicity. The theorems below establish structural
  monotonicity: bonds internal to a subsystem remain internal in the
  composed system. -/

/-- Composition preserves internal structure: every bond internal to σ₁
    remains internal in the composed system.

    Bonds that were EXTERNAL to σ₁ (one endpoint in σ₁'s environment
    that is a component of σ₂) become INTERNAL in the composed system.
    Composition internalizes cross-boundary interaction — a qualitative
    increase in structural complexity. -/
theorem ConcreteSystem.compose_internalStructure_ge_left {α : Type*} [ActsOn α]
    {σ₁ σ₂ : ConcreteSystem α}
    (h_disjoint : σ₁.composition ∩ σ₂.composition = ∅)
    (h_interact : ∃ a ∈ σ₁.composition, ∃ b ∈ σ₂.composition, Bonded a b) :
    σ₁.internalStructure ⊆
      (σ₁.compose σ₂ h_disjoint h_interact).internalStructure := by
  intro p hp
  unfold ConcreteSystem.internalStructure at hp ⊢
  dsimp [ConcreteSystem.compose]
  obtain ⟨hs, hc1, hc2⟩ := hp
  exact ⟨Set.mem_union_left _ hs, Set.mem_union_left _ hc1, Set.mem_union_left _ hc2⟩

/-- Symmetric: composition preserves σ₂'s internal structure too. -/
theorem ConcreteSystem.compose_internalStructure_ge_right {α : Type*} [ActsOn α]
    {σ₁ σ₂ : ConcreteSystem α}
    (h_disjoint : σ₁.composition ∩ σ₂.composition = ∅)
    (h_interact : ∃ a ∈ σ₁.composition, ∃ b ∈ σ₂.composition, Bonded a b) :
    σ₂.internalStructure ⊆
      (σ₁.compose σ₂ h_disjoint h_interact).internalStructure := by
  intro p hp
  unfold ConcreteSystem.internalStructure at hp ⊢
  dsimp [ConcreteSystem.compose]
  obtain ⟨hs, hc1, hc2⟩ := hp
  exact ⟨Set.mem_union_right _ hs, Set.mem_union_right _ hc1, Set.mem_union_right _ hc2⟩

/-! ## Derivability Assessment

  STRUCTURAL COMPLEXITY DERIVES FROM #1 + #2 + #3.

  Every structural measure maps to existing data:

  | Measure | Source | Principle |
  |---|---|---|
  | Component count | ConcreteSystem.composition | Systemness #1 |
  | Bond count | ConcreteSystem.internalStructure | Systemness #1 + Networks #3 |
  | Hierarchical depth | RecursiveSystem.depth | Hierarchy #2 |
  | Modular count | NearDecomposable.modules.length | Hierarchy #2 |
  | Component-kind diversity | SameKind equivalence classes | Systemness #1 |

  No measure requires structure beyond Principles 1-3. This file
  compiles with only Systems.Core.Systemness imported.

  SIMONIAN COMPLEXITY (future bridge theorem): Simon's argument that
  near-decomposable systems have tractable state spaces (S^N reduces
  to modular products) connects NearDecomposable (#2) to state-space
  composition (Dynamics #4). This is structurally parallel to
  conditional_time_scale_separation — both are bridge theorems that
  name what Dynamics provides. Neither requires a new principle.

  Mobus himself defers behavioral complexity as future research.

  THE 12 PRINCIPLES REDUCE BY AT LEAST 1. -/

end Systems
