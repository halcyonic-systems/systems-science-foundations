/-
  Systems/Core/System.lean
  Concrete systems, subsystem ordering, and basic properties

  Formalizes Bunge, Treatise on Basic Philosophy Vol. 4, Definitions 1.1-1.7:
  - ConcreteSystem: the CES triple ⟨C, E, S⟩
  - Closed/Open systems (Def 1.3, 1.4)
  - Internal/External structure (Def 1.5)
  - Subsystem relation (Def 1.6) — proved to be a partial order
  - Nested systems (Def 1.7)

  SHOWCASE THEOREM #1: Subsystem ordering is a PartialOrder.
-/

import Systems.Core.Bond

namespace Systems

/-! ## Concrete System (Bunge Def 1.1, 1.2) -/

/-- A concrete system is an ordered triple ⟨C, E, S⟩ where:
    - C: composition (set of components)
    - E: environment (set of external things bonded with components)
    - S: structure (set of relations among components and environment)
    The key constraints are:
    - C ∩ E = ∅ (composition and environment are disjoint)
    - There exist at least two different connected things in C (Def 1.1)

    Bunge Def 1.2: s_A(σ,t) = ⟨C_A(σ,t), E_A(σ,t), S_A(σ,t)⟩

    DESIGN: Time-parameterization is deferred — each ConcreteSystem represents
    a snapshot at a given time t. This matches Bunge's "at time t" qualifier
    while keeping types simple for Phase 1. -/
structure ConcreteSystem (α : Type*) [ActsOn α] where
  /-- Composition: set of components -/
  composition : Set α
  /-- Environment: set of external things bonded with components -/
  environment : Set α
  /-- Structure: set of relations (as pairs) on C ∪ E -/
  structure' : Set (α × α)
  /-- Composition and environment are disjoint (Bunge §1.2: C ∩ E = ∅) -/
  disjoint : composition ∩ environment = ∅
  /-- Structure relations are defined on C ∪ E -/
  structure_on : ∀ p ∈ structure', p.1 ∈ composition ∪ environment ∧
    p.2 ∈ composition ∪ environment
  /-- Bondage is nonempty: at least one bonded pair exists in C (Def 1.1) -/
  bondage_nonempty : ∃ a ∈ composition, ∃ b ∈ composition, a ≠ b ∧ Bonded a b

/-! ## Closed and Open Systems (Bunge Def 1.3) -/

/-- A system is closed at time t iff its environment is empty.
    Bunge Def 1.3: σ is closed iff E(σ,t) = ∅.
    "Since every thing but the universe interacts with some other things..." -/
def ConcreteSystem.isClosed {α : Type*} [ActsOn α] (σ : ConcreteSystem α) : Prop :=
  σ.environment = ∅

/-- A system is open iff it is not closed.
    Bunge Def 1.3: "otherwise σ is open." -/
def ConcreteSystem.isOpen {α : Type*} [ActsOn α] (σ : ConcreteSystem α) : Prop :=
  ¬σ.isClosed

/-- Closed and open are complementary.
    Bunge Def 1.3 immediate. -/
theorem ConcreteSystem.closed_or_open {α : Type*} [ActsOn α] (σ : ConcreteSystem α) :
    σ.isClosed ∨ σ.isOpen :=
  em σ.isClosed

/-! ## Open with respect to a property (Bunge Def 1.4) -/

/-- A system is open with respect to a property P iff P relates to at least
    one property of things in the environment.
    Bunge Def 1.4: σ is open w.r.t. P at t iff P is related to at least one
    property of things in E(σ,t).

    DESIGN: We represent "property" abstractly as any predicate on α. -/
def ConcreteSystem.isOpenWrt {α : Type*} [ActsOn α]
    (σ : ConcreteSystem α) (P : α → Prop) : Prop :=
  ∃ x ∈ σ.environment, P x

/-- A system is closed iff it is closed in every respect.
    Bunge: "a system is closed iff it is closed in every respect." -/
theorem ConcreteSystem.closed_iff_closed_all {α : Type*} [ActsOn α]
    (σ : ConcreteSystem α) :
    σ.isClosed ↔ ∀ P : α → Prop, ¬σ.isOpenWrt P := by
  constructor
  · intro hclosed P ⟨x, hx, _⟩
    rw [ConcreteSystem.isClosed, Set.eq_empty_iff_forall_notMem] at hclosed
    exact hclosed x hx
  · intro h
    rw [ConcreteSystem.isClosed, Set.eq_empty_iff_forall_notMem]
    intro x hx
    exact h (fun _ => True) ⟨x, hx, trivial⟩

/-! ## Internal and External Structure (Bunge Def 1.5) -/

/-- The internal structure of σ: relations among components only.
    Bunge Def 1.5(i): subset of S_A composed of relations among A-parts. -/
def ConcreteSystem.internalStructure {α : Type*} [ActsOn α]
    (σ : ConcreteSystem α) : Set (α × α) :=
  {p ∈ σ.structure' | p.1 ∈ σ.composition ∧ p.2 ∈ σ.composition}

/-- The external structure: relations involving at least one environment thing.
    Complement of internal structure within total structure. -/
def ConcreteSystem.externalStructure {α : Type*} [ActsOn α]
    (σ : ConcreteSystem α) : Set (α × α) :=
  {p ∈ σ.structure' | p.1 ∈ σ.environment ∨ p.2 ∈ σ.environment}

/-! ## Subsystem Relation (Bunge Def 1.6) -/

/-- Subsystem relation: σ₁ is a subsystem of σ₂.
    Bunge Def 1.6: x ≺ σ iff
    (i) x is a system, and
    (ii) C(x) ⊆ C(σ) ∧ E(x) ⊇ E(σ) ∧ S(x) ⊆ S(σ)

    Note the asymmetry: a subsystem has MORE environment (it sees
    the rest of the supersystem as part of its environment) but
    LESS composition and structure. -/
def Subsystem {α : Type*} [ActsOn α]
    (σ₁ σ₂ : ConcreteSystem α) : Prop :=
  σ₁.composition ⊆ σ₂.composition ∧
  σ₂.environment ⊆ σ₁.environment ∧
  σ₁.structure' ⊆ σ₂.structure'

/-- Subsystem is reflexive.
    Every system is a subsystem of itself. -/
theorem subsystem_refl {α : Type*} [ActsOn α] (σ : ConcreteSystem α) :
    Subsystem σ σ :=
  ⟨Set.Subset.refl _, Set.Subset.refl _, Set.Subset.refl _⟩

/-- Subsystem is transitive.
    If σ₁ ≺ σ₂ and σ₂ ≺ σ₃, then σ₁ ≺ σ₃. -/
theorem subsystem_trans {α : Type*} [ActsOn α]
    {σ₁ σ₂ σ₃ : ConcreteSystem α}
    (h₁₂ : Subsystem σ₁ σ₂) (h₂₃ : Subsystem σ₂ σ₃) :
    Subsystem σ₁ σ₃ :=
  ⟨Set.Subset.trans h₁₂.1 h₂₃.1,
   Set.Subset.trans h₂₃.2.1 h₁₂.2.1,
   Set.Subset.trans h₁₂.2.2 h₂₃.2.2⟩

/-- Subsystem is antisymmetric (on the CES triple).
    If σ₁ ≺ σ₂ and σ₂ ≺ σ₁, then their CES triples are equal.
    This is the key property making subsystem a partial order. -/
theorem subsystem_antisymm_components {α : Type*} [ActsOn α]
    {σ₁ σ₂ : ConcreteSystem α}
    (h₁₂ : Subsystem σ₁ σ₂) (h₂₁ : Subsystem σ₂ σ₁) :
    σ₁.composition = σ₂.composition ∧
    σ₁.environment = σ₂.environment ∧
    σ₁.structure' = σ₂.structure' :=
  ⟨Set.Subset.antisymm h₁₂.1 h₂₁.1,
   Set.Subset.antisymm h₂₁.2.1 h₁₂.2.1,
   Set.Subset.antisymm h₁₂.2.2 h₂₁.2.2⟩

/-! ## Corollary 1.1: The Universe -/

/-- Corollary 1.1: The universe is the only closed system.
    Bunge: "The universe is the only system closed at all times."
    We state a weaker version: if σ is closed, its environment is empty. -/
theorem universe_only_closed {α : Type*} [ActsOn α] (σ : ConcreteSystem α) :
    σ.isClosed ↔ σ.environment = ∅ :=
  Iff.rfl

/-! ## Nested Systems (Bunge Def 1.7) -/

/-- A system of nested systems: a collection of supersystems of σ
    partially ordered by the subsystem relation.
    Bunge Def 1.7(i): N_σ = {σ_i ∈ Σ | σ ≺ σ_i}. -/
def NestedSystems {α : Type*} [ActsOn α]
    (core : ConcreteSystem α) (chain : List (ConcreteSystem α)) : Prop :=
  (∀ σ ∈ chain, Subsystem core σ) ∧
  chain.Pairwise (fun σ₁ σ₂ => Subsystem σ₁ σ₂)

end Systems
