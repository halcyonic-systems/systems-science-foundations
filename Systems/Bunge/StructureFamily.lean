/-
  Systems/Bunge/StructureFamily.lean
  EXPLORATORY — investigating a richer Bunge structure representation

  STATUS: Experimental. NOT imported by any main module. Build with:
    lake build Systems.Bunge.StructureFamily

  QUESTION: Bunge's "structure" S is formalized as `Set (α × α)` — a single
  flat set of pairs. But Bunge actually writes (Def 1.2, Vol. 4):

    S_A(σ,t) = "the set of relations among components and environment"

  "Set of *relations*" — plural. Each relation is itself a set of pairs.
  So the faithful reading is S = {S_i} where each S_i ⊆ (C ∪ E) × (C ∪ E).
  This is exactly the question Joslyn asked (p. 7 feedback):

    "What do you mean more precisely? 'Set of relations' literally means
     S is a set of sets of tuples, right?"

  The current formalization collapses this to `Set (α × α)` — flattening
  the family into a single relation. This file investigates: what if we
  keep the family structure? What breaks, what new theorems become provable,
  what gets harder?

  FINDINGS (documented inline as we go):
-/

import Systems.Klir.KlirSystem
import Mathlib.Data.Set.Lattice

namespace Systems

/-! ## Rich Structure: A Family of Named Relations -/

/-- A "rich" concrete system that preserves Bunge's "set of relations"
    as a family of relations, not a single flattened relation.

    Each element of `structureFamily` is a distinct relation (e.g.,
    "energy flow", "information flow", "control relation") — each
    is a set of pairs on C ∪ E.

    Compare with `ConcreteSystem` where `structure' : Set (α × α)`
    is a single flat set. -/
structure RichConcreteSystem (α : Type*) [ActsOn α] where
  /-- Composition: set of components (same as ConcreteSystem) -/
  composition : Set α
  /-- Environment: set of external things (same as ConcreteSystem) -/
  environment : Set α
  /-- Structure family: a SET of relations, each a set of pairs on C ∪ E.
      This is the faithful reading of Bunge's "set of relations". -/
  structureFamily : Set (Set (α × α))
  /-- Composition and environment are disjoint -/
  disjoint : composition ∩ environment = ∅
  /-- Every relation in the family is defined on C ∪ E -/
  family_on : ∀ R ∈ structureFamily, ∀ p ∈ R,
    p.1 ∈ composition ∪ environment ∧ p.2 ∈ composition ∪ environment
  /-- At least two bonded components (same requirement as ConcreteSystem) -/
  bondage_nonempty : ∃ a ∈ composition, ∃ b ∈ composition, a ≠ b ∧ Bonded a b

/-! ## Flatten: RichConcreteSystem → ConcreteSystem

    FINDING 1: Flattening is straightforward — take the union of all
    relations in the family. The `structure_on` constraint follows from
    `family_on` by pushing through the union. -/

/-- Flatten the structure family into a single relation by union. -/
def RichConcreteSystem.flatten {α : Type*} [ActsOn α]
    (r : RichConcreteSystem α) : Set (α × α) :=
  ⋃₀ r.structureFamily

/-- The flattened relation is defined on C ∪ E.
    Follows from each family member being on C ∪ E. -/
theorem RichConcreteSystem.flatten_on {α : Type*} [ActsOn α]
    (r : RichConcreteSystem α) :
    ∀ p ∈ r.flatten, p.1 ∈ r.composition ∪ r.environment ∧
      p.2 ∈ r.composition ∪ r.environment := by
  intro p hp
  simp only [RichConcreteSystem.flatten, Set.mem_sUnion] at hp
  obtain ⟨S, hS, hp⟩ := hp
  exact r.family_on S hS p hp

/-- Project a RichConcreteSystem to a ConcreteSystem by flattening. -/
def RichConcreteSystem.toConcreteSystem {α : Type*} [ActsOn α]
    (r : RichConcreteSystem α) : ConcreteSystem α where
  composition := r.composition
  environment := r.environment
  structure' := r.flatten
  disjoint := r.disjoint
  structure_on := r.flatten_on
  bondage_nonempty := r.bondage_nonempty

/-! ## FINDING 2: Internal and external structure decompose PER RELATION.

    With a structure family, we can define internal/external structure
    for each individual relation — not just for the aggregate. This is
    genuinely new: you can ask "which energy-flow pairs are internal?"
    separately from "which information-flow pairs are internal?" -/

/-- The internal projection of a single relation: pairs among components only. -/
def internalProjection {α : Type*} (composition : Set α) (R : Set (α × α)) :
    Set (α × α) :=
  {p ∈ R | p.1 ∈ composition ∧ p.2 ∈ composition}

/-- The external projection: pairs involving at least one environment element. -/
def externalProjection {α : Type*} (environment : Set α) (R : Set (α × α)) :
    Set (α × α) :=
  {p ∈ R | p.1 ∈ environment ∨ p.2 ∈ environment}

/-- The family of internal structures: one per relation in the family.
    Each member tells you which pairs of THAT relation are among components. -/
def RichConcreteSystem.internalFamily {α : Type*} [ActsOn α]
    (r : RichConcreteSystem α) : Set (Set (α × α)) :=
  (internalProjection r.composition) '' r.structureFamily

/-- The family of external structures: one per relation in the family. -/
def RichConcreteSystem.externalFamily {α : Type*} [ActsOn α]
    (r : RichConcreteSystem α) : Set (Set (α × α)) :=
  (externalProjection r.environment) '' r.structureFamily

/-! ## FINDING 3: Flatten commutes with internal/external projection.

    The internal structure of the flattened system equals the flatten
    of the internal family. This is a nice sanity check: the two
    ways of getting "all internal pairs" are consistent.

    ⋃ (internal R_i) = internal (⋃ R_i)

    This means the flat ConcreteSystem's `internalStructure` is
    faithfully recovered from the family version. No information
    about internal-vs-external is lost by flattening — because
    that distinction is determined by membership in C, not by
    which named relation a pair belongs to. -/

/-- Flattening commutes with internal projection. -/
theorem flatten_internal_commutes {α : Type*} [ActsOn α]
    (r : RichConcreteSystem α) :
    ⋃₀ r.internalFamily =
    internalProjection r.composition r.flatten := by
  ext p
  simp only [Set.mem_sUnion, RichConcreteSystem.internalFamily,
    Set.mem_image, internalProjection,
    RichConcreteSystem.flatten]
  constructor
  · rintro ⟨S, ⟨T, hT, rfl⟩, hp⟩
    exact ⟨⟨T, hT, hp.1⟩, hp.2⟩
  · rintro ⟨⟨T, hT, hpT⟩, hcomp⟩
    exact ⟨internalProjection r.composition T, ⟨T, hT, rfl⟩, hpT, hcomp⟩

/-- Flattening commutes with external projection. -/
theorem flatten_external_commutes {α : Type*} [ActsOn α]
    (r : RichConcreteSystem α) :
    ⋃₀ r.externalFamily =
    externalProjection r.environment r.flatten := by
  ext p
  simp only [Set.mem_sUnion, RichConcreteSystem.externalFamily,
    Set.mem_image, externalProjection,
    RichConcreteSystem.flatten]
  constructor
  · rintro ⟨S, ⟨T, hT, rfl⟩, hp⟩
    exact ⟨⟨T, hT, hp.1⟩, hp.2⟩
  · rintro ⟨⟨T, hT, hpT⟩, henv⟩
    exact ⟨externalProjection r.environment T, ⟨T, hT, rfl⟩, hpT, henv⟩

/-! ## Subsystem Ordering on Rich Systems

    FINDING 4: The subsystem relation on RichConcreteSystem is less
    obvious than on ConcreteSystem. With a flat structure, subsystem
    requires S₁ ⊆ S₂ (simple set inclusion). With a family, there
    are at least two plausible definitions:

    (a) FLAT SUBSYSTEM: flatten(F₁) ⊆ flatten(F₂)
        — the aggregate relation is a subset
        — ignores which named relation each pair belongs to
        — equivalent to ConcreteSystem subsystem after projection

    (b) FAMILY SUBSYSTEM: ∀ R ∈ F₁, R ∈ F₂
        — every relation in the smaller system appears in the larger
        — preserves the named-relation structure
        — strictly stronger than (a)

    (c) REFINEMENT SUBSYSTEM: ∀ R₁ ∈ F₁, ∃ R₂ ∈ F₂, R₁ ⊆ R₂
        — each relation in the smaller system is contained in some
          relation of the larger system
        — a middle ground: preserves some structure but allows
          splitting/merging of named relations

    INSIGHT: Bunge's Def 1.6 uses flat inclusion. If you upgrade to
    family, you need to choose. Family subsystem (b) is the most
    faithful to "structure is a set of relations, and a subsystem has
    fewer relations." But it's also the most restrictive. -/

/-- Option (a): flat subsystem — checks the aggregate only. -/
def RichSubsystem_flat {α : Type*} [ActsOn α]
    (σ₁ σ₂ : RichConcreteSystem α) : Prop :=
  σ₁.composition ⊆ σ₂.composition ∧
  σ₂.environment ⊆ σ₁.environment ∧
  σ₁.flatten ⊆ σ₂.flatten

/-- Option (b): family subsystem — every relation appears. -/
def RichSubsystem_family {α : Type*} [ActsOn α]
    (σ₁ σ₂ : RichConcreteSystem α) : Prop :=
  σ₁.composition ⊆ σ₂.composition ∧
  σ₂.environment ⊆ σ₁.environment ∧
  σ₁.structureFamily ⊆ σ₂.structureFamily

/-- Option (c): refinement subsystem — each relation is contained. -/
def RichSubsystem_refinement {α : Type*} [ActsOn α]
    (σ₁ σ₂ : RichConcreteSystem α) : Prop :=
  σ₁.composition ⊆ σ₂.composition ∧
  σ₂.environment ⊆ σ₁.environment ∧
  ∀ R₁ ∈ σ₁.structureFamily, ∃ R₂ ∈ σ₂.structureFamily, R₁ ⊆ R₂

/-- Family subsystem implies refinement subsystem. -/
theorem family_implies_refinement {α : Type*} [ActsOn α]
    (σ₁ σ₂ : RichConcreteSystem α)
    (h : RichSubsystem_family σ₁ σ₂) :
    RichSubsystem_refinement σ₁ σ₂ :=
  ⟨h.1, h.2.1, fun R hR => ⟨R, h.2.2 hR, Set.Subset.refl _⟩⟩

/-- Refinement subsystem implies flat subsystem.
    If every R₁ ∈ F₁ is contained in some R₂ ∈ F₂,
    then ⋃F₁ ⊆ ⋃F₂. -/
theorem refinement_implies_flat {α : Type*} [ActsOn α]
    (σ₁ σ₂ : RichConcreteSystem α)
    (h : RichSubsystem_refinement σ₁ σ₂) :
    RichSubsystem_flat σ₁ σ₂ := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro p hp
  simp only [RichConcreteSystem.flatten, Set.mem_sUnion] at hp ⊢
  obtain ⟨R₁, hR₁, hp₁⟩ := hp
  obtain ⟨R₂, hR₂, hle⟩ := h.2.2 R₁ hR₁
  exact ⟨R₂, hR₂, hle hp₁⟩

/-! ## FINDING 5: Flat subsystem preserves through toConcreteSystem.

    The projection to ConcreteSystem preserves flat subsystem ordering.
    This means the commuting triangle still works if you use flat
    subsystem. -/

/-- Flat subsystem on RichConcreteSystem projects to Bunge Subsystem. -/
theorem flat_subsystem_preserved {α : Type*} [ActsOn α]
    (σ₁ σ₂ : RichConcreteSystem α)
    (h : RichSubsystem_flat σ₁ σ₂) :
    Subsystem σ₁.toConcreteSystem σ₂.toConcreteSystem :=
  ⟨h.1, h.2.1, h.2.2⟩

/-! ## Connection to Klir: Does the Commuting Triangle Survive?

    FINDING 6: Yes. The enrichment is ABOVE ConcreteSystem in the
    information hierarchy:

      RichConcreteSystem → ConcreteSystem → KlirSystem

    The first arrow (flatten) loses named-relation structure.
    The second arrow (toKlir) loses environment.

    The commuting triangle (Mobus → Bunge → Klir = Mobus → Klir)
    operates at the ConcreteSystem level. Adding a RichConcreteSystem
    layer above it doesn't affect the triangle — it adds a fourth
    node to the diagram:

      Rich → Bunge → Klir

    And the question becomes: does Mobus's 8-tuple project to
    a RichConcreteSystem? If so, the diagram extends:

      Mobus → Rich → Bunge → Klir = Mobus → Klir

    The answer is yes — Mobus's internal and external networks
    are naturally two distinct relations, giving a 2-element family. -/

/-- Project a RichConcreteSystem to a KlirSystem by flattening then
    forgetting environment. -/
def RichConcreteSystem.toKlir {α : Type*} [ActsOn α]
    (r : RichConcreteSystem α) : KlirSystem α where
  things := r.composition
  relation := r.flatten

/-- The two ways of reaching KlirSystem agree:
    Rich → Bunge → Klir = Rich → Klir. -/
theorem rich_triangle_commutes {α : Type*} [ActsOn α]
    (r : RichConcreteSystem α) :
    r.toConcreteSystem.toKlir = r.toKlir := rfl

/-! ## FINDING 7: What new theorems become provable?

    With a structure family, we can state properties that the flat
    representation cannot:

    (a) RELATION COUNTING: |F| gives the number of distinct types
        of interaction. A system with 3 relations (energy, information,
        material) is structurally different from one with 1 (aggregate)
        even if the union is the same set of pairs. The flat representation
        cannot distinguish these.

    (b) RELATION-SPECIFIC PROPERTIES: Each relation in the family can
        have its own properties (symmetry, transitivity, reflexivity).
        "Energy flow is asymmetric but information flow is symmetric"
        is expressible per-relation but not in the flat aggregate.

    (c) INDEPENDENCE: Two relations R₁, R₂ ∈ F are independent if
        R₁ ∩ R₂ = ∅. This means the corresponding interaction types
        never co-occur on the same pair. The flat representation loses
        this entirely.

    (d) COVERAGE: Every pair in C × C appears in at least one relation.
        This is a completeness condition that's meaningful per-relation
        but tautological in the flat version.
-/

/-- Two relations in the family are independent if they share no pairs. -/
def RelationsIndependent {α : Type*} (R₁ R₂ : Set (α × α)) : Prop :=
  R₁ ∩ R₂ = ∅

/-- A structure family has full internal coverage if every component pair
    appears in at least one relation. -/
def FullInternalCoverage {α : Type*} [ActsOn α]
    (r : RichConcreteSystem α) : Prop :=
  ∀ a ∈ r.composition, ∀ b ∈ r.composition, a ≠ b →
    ∃ R ∈ r.structureFamily, (a, b) ∈ R

/-- A relation in the family is symmetric. -/
def RelationSymmetric {α : Type*} (R : Set (α × α)) : Prop :=
  ∀ p ∈ R, (p.2, p.1) ∈ R

/-- A relation in the family is antisymmetric. -/
def RelationAntisymmetric {α : Type*} (R : Set (α × α)) : Prop :=
  ∀ p ∈ R, (p.2, p.1) ∈ R → p.1 = p.2

/-! ## FINDING 8: What gets harder?

    (a) SUBSYSTEM ORDERING: As shown in Finding 4, the subsystem
        relation now has multiple plausible definitions. Bunge's
        clean partial order on flat structure (`S₁ ⊆ S₂`) bifurcates
        into a family of options. The flat version (a) is still a
        partial order, but options (b) and (c) need separate proofs.

    (b) INSTANTIATION: Creating a RichConcreteSystem requires providing
        a `Set (Set (α × α))` with `family_on` proved for every member.
        This is more work than providing a single `Set (α × α)`. For
        examples with named relations (energy, information, etc.) this
        is natural. For abstract proofs, it adds friction.

    (c) BRIDGE FROM MOBUS: The current Bridge.lean produces a flat
        ConcreteSystem. To produce a RichConcreteSystem, we'd need to
        split Mobus's totalRelation back into its constituent networks
        — internal and external. This is possible (they're separate
        fields in MobusSystem) but the bridge becomes a 2-element family
        constructor, not a simple field copy.

    (d) KLIR PROJECTION: Going Rich → Klir requires flattening. If
        any theorem depends on family structure, it's lost. The Klir
        level is inherently flat — (T, R) has one relation.

    VERDICT: The structure family is a genuine enrichment that sits
    naturally between Mobus's 8-tuple and Bunge's CES triple. It
    captures information that both the current flat encoding AND
    Klir's (T, R) lose. Whether it's worth integrating depends on
    whether the paper needs to address Joslyn's "set of relations"
    question with a TYPE-LEVEL answer (yes, we can) rather than a
    COMMENT-LEVEL answer (we chose to flatten). For the AITP and
    ISSS deadlines, the flat encoding is sufficient. For the journal
    paper responding to Joslyn, the family encoding answers his
    question directly.
-/

/-! ## Mobus → RichConcreteSystem: The 2-Relation Bridge

    FINDING 9: Mobus's 8-tuple naturally gives a 2-element structure
    family: {internal network relation, external flow relation}. This
    is richer than the flat ConcreteSystem (which unions them) but
    less rich than a domain-specific family (which might distinguish
    energy, information, material, etc.). -/

/-- Project a Mobus 8-tuple to a RichConcreteSystem with a 2-element
    structure family: {internal edges, external edges}.

    This preserves the internal/external distinction that the flat
    toBunge discards when it takes their union as totalRelation. -/
def MobusSystem.toRichBunge {α κ μ π τ η δ : Type*} [ActsOn α]
    (sys : MobusSystem α κ μ π τ η δ)
    (hflow : FlowInducesAction sys.internalNetwork)
    (hedge : sys.internalNetwork.edges.Nonempty) :
    RichConcreteSystem α where
  composition := sys.components
  environment := sys.environment.objects
  structureFamily := {sys.internalNetwork.toRelation, sys.externalFlows.toRelation}
  disjoint := sys.disjoint
  family_on := by
    intro R hR p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hR
    rcases hR with rfl | rfl
    · -- Internal network relation: both endpoints in components
      have hon := sys.internalNetwork.toRelation_on p hp
      rw [sys.network_components] at hon
      exact ⟨Set.mem_union_left _ hon.1, Set.mem_union_left _ hon.2⟩
    · -- External flows relation: endpoints in env ∪ interfaces ⊆ env ∪ components
      have hon := sys.externalFlows.toRelation_on p hp
      constructor
      · rcases Set.mem_of_subset_of_mem sys.externalFlows_nodes hon.1 with h | h
        · exact Set.mem_union_right _ h
        · exact Set.mem_union_left _ (sys.interfaces_sub h)
      · rcases Set.mem_of_subset_of_mem sys.externalFlows_nodes hon.2 with h | h
        · exact Set.mem_union_right _ h
        · exact Set.mem_union_left _ (sys.interfaces_sub h)
  bondage_nonempty := by
    obtain ⟨e, he⟩ := hedge
    have hon := sys.internalNetwork.edges_on e he
    rw [sys.network_components] at hon
    exact ⟨e.source, hon.1, e.target, hon.2,
           sys.internalNetwork.no_self_loops e he,
           Or.inl (hflow e he)⟩

/-! ## FINDING 10: The extended diagram commutes.

    Mobus → RichBunge → ConcreteSystem → Klir = Mobus → Klir

    All four paths to KlirSystem give the same result:
    - Mobus → Bunge → Klir (original triangle)
    - Mobus → Rich → Bunge → Klir (through the family)
    - Mobus → Rich → Klir (family then direct)
    - Mobus → Klir (direct)

    The key insight: flatten of {internal, external} = totalRelation.
    This is because Set.sUnion_pair gives ⋃₀{A, B} = A ∪ B, and
    totalRelation is defined as the union of internal and external
    edge-pair sets. -/

/-- The flatten of the 2-element family equals the original totalRelation. -/
theorem MobusSystem.toRichBunge_flatten_eq {α κ μ π τ η δ : Type*} [ActsOn α]
    (sys : MobusSystem α κ μ π τ η δ)
    (hf : FlowInducesAction sys.internalNetwork)
    (hg : sys.internalNetwork.edges.Nonempty) :
    (sys.toRichBunge hf hg).flatten = sys.totalRelation := by
  simp only [RichConcreteSystem.flatten, MobusSystem.toRichBunge,
    MobusSystem.totalRelation, Set.sUnion_pair]

/-! ## Summary of Findings

    1. FLATTEN IS CLEAN: RichConcreteSystem → ConcreteSystem via ⋃ is
       well-defined and preserves all constraints.

    2. PER-RELATION PROJECTIONS: Internal/external structure can be
       computed per relation, not just in aggregate.

    3. FLATTEN COMMUTES: ⋃(internal R_i) = internal(⋃ R_i). No
       information about internal-vs-external is lost by flattening.

    4. SUBSYSTEM ORDERING BIFURCATES: Three plausible definitions,
       forming a strict hierarchy: family ⊂ refinement ⊂ flat.

    5. FLAT SUBSYSTEM PRESERVED: Projects cleanly to Bunge's Subsystem.

    6. COMMUTING TRIANGLE SURVIVES: Rich → Bunge → Klir = Rich → Klir
       by rfl (adding a family layer above doesn't affect the triangle).

    7. NEW EXPRESSIVE POWER: Relation counting, per-relation properties,
       independence, coverage — all impossible in the flat encoding.

    8. FRICTION COSTS: Harder instantiation, subsystem ambiguity,
       bridge complexity, Klir inherently loses family structure.

    9. MOBUS BRIDGE: Natural 2-element family {internal, external}.

   10. EXTENDED DIAGRAM COMMUTES: Four paths to Klir all agree.

   RECOMMENDATION: Keep flat encoding for AITP/ISSS deadlines.
   Add StructureFamily as a remark in the journal paper responding
   to Joslyn's comment A1. The type-level answer ("we can represent
   S as Set (Set (α × α))") is more satisfying than the comment-level
   answer ("we chose to flatten"), and the flatten-commutes theorem
   shows nothing is lost for the results we actually prove.
-/

end Systems
