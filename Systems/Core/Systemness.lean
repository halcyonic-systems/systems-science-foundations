/-
  Systems/Core/Systemness.lean
  Principle 1: Systemness — recursive systems with CES constraints at every level

  Formalizes Mobus, Systems Science: Theory, Analysis, Modeling, and Design, §2.3.1:
  "Bounded networks of relations among parts constitute a holistic unit.
   Systems interact with other systems, forming yet larger systems.
   The Universe is composed of systems of systems."

  The central claim: every component of a system is either a process
  primitive (atomic, no further decomposition) or is itself a system
  with full CES constraints — composition, environment, structure,
  disjointness, and nonempty bondage. This is Mobus Eq. 4.3 enriched
  with Bunge's system semantics at every level.

  Key definitions:
  - RecursiveSystem: inductive type where each composite level carries
    a ConcreteSystem
  - WellFormed: recursive predicate ensuring children biject with
    composition at every level
  - IsOrganized / IsAggregate: the "organized vs. heaped" distinction

  Key theorems:
  - Decomposition terminates (from inductive type)
  - Every composite level has organized composition (from ConcreteSystem)
  - Well-formedness propagates to children

  DESIGN NOTES:

  We use ConcreteSystem (Bunge CES triple) rather than MobusSystem
  (8-tuple) at each level. Systemness as a principle is about what
  makes something a system vs. an aggregate: composition, bonds,
  environment. The 8-tuple adds operational content (flow networks,
  boundary properties, transforms, history, time scale) belonging to
  later principles — Networks (#3), Dynamics (#4), Information (#7).
  Bridge.lean projects MobusSystem → ConcreteSystem preserving
  subsystem ordering, so results here lift to the 8-tuple.

  The inductive type carries data only; constraints linking children
  to composition live in the separate WellFormed predicate. This is
  forced by Lean 4's kernel: nested inductive types cannot contain
  existentials over the type being defined.

  The `thing : α` field on composite nodes represents the system's
  identity as a discrete entity in the universe of discourse. This
  is well-defined for crisp, well-bounded concrete systems (Mobus's
  primary subject). Two cases where it becomes strained:

  1. Fuzzy systems (Mobus §2.2): when the boundary is an analytical
     choice rather than an ontological fact, the system may lack a
     crisp thing-identity. A future FuzzyRecursiveSystem could weaken
     `thing : α` to a membership degree, but this is beyond Principle 1.

  2. Top-level systems: Bunge asserts the universe is the only closed
     system (Corollary 1.1). Whether the universe is truly closed is
     philosophically contested — Smolin's cosmological natural selection,
     multiverse hypotheses, and open-boundary cosmologies all challenge
     closure. In our formalization, a top-level RecursiveSystem has a
     `thing : α` that no parent's composition references. This is not
     a defect — it reflects that the root of any decomposition tree has
     no containing system within the model's scope. We do NOT assume
     the universe is closed; we only note that the top-level node's
     `thing` is structurally orphaned.
-/

import Systems.Core.System
import Systems.Core.Level

namespace Systems

/-! ## RecursiveSystem -/

/-- A recursive system: Mobus Eq. 4.3 enriched with Bunge's CES constraints.

    Each node is either:
    - `primitive`: a process primitive (atomic work process, terminal)
    - `composite`: a system with full CES constraints whose components
      are themselves RecursiveSystem nodes

    The existing `RecursiveComponent` captures the tree shape without
    system semantics. `RecursiveSystem` adds the CES constraints that
    make each composite level a genuine system, not just a tree node.

    Constraints linking children to composition are in `WellFormed`
    (Lean 4's kernel requires separating existential proof fields from
    the inductive type definition).

    Decomposition terminates by Lean's structural recursion on the
    inductive type — no explicit well-foundedness proof needed. -/
inductive RecursiveSystem (α : Type*) [ActsOn α] where
  /-- A process primitive: terminal component, no further decomposition.
      These are the atomic work processes at the bottom of every
      decomposition hierarchy. -/
  | primitive (thing : α) : RecursiveSystem α
  /-- A composite system: carries a full ConcreteSystem with CES
      constraints, whose components are themselves RecursiveSystem nodes.
      The `thing` field is this system's identity when viewed as a
      component in its parent's composition. -/
  | composite
      (thing : α)
      (system : ConcreteSystem α)
      (children : List (RecursiveSystem α))
      : RecursiveSystem α

/-- The thing represented by a recursive system node. -/
def RecursiveSystem.thing {α : Type*} [ActsOn α] : RecursiveSystem α → α
  | .primitive a => a
  | .composite a _ _ => a

/-- Whether a node is a process primitive (leaf). -/
def RecursiveSystem.isPrimitive {α : Type*} [ActsOn α] :
    RecursiveSystem α → Bool
  | .primitive _ => true
  | .composite _ _ _ => false

/-- Whether a node is composite (has internal structure). -/
def RecursiveSystem.isComposite {α : Type*} [ActsOn α] :
    RecursiveSystem α → Bool
  | .primitive _ => false
  | .composite _ _ _ => true

/-- The depth of a recursive system (height of the decomposition tree).
    Process primitives have depth 0. -/
def RecursiveSystem.depth {α : Type*} [ActsOn α] :
    RecursiveSystem α → Nat
  | .primitive _ => 0
  | .composite _ _ children =>
      1 + children.foldl (fun acc c => max acc c.depth) 0

/-- Count the total number of process primitives (leaf nodes). -/
def RecursiveSystem.primitiveCount {α : Type*} [ActsOn α] :
    RecursiveSystem α → Nat
  | .primitive _ => 1
  | .composite _ _ children =>
      children.foldl (fun acc c => acc + c.primitiveCount) 0

/-! ## Well-Formedness

  The inductive type carries data; the WellFormed predicate ensures
  that at each composite level, the children's things biject with the
  system's composition. This is the constraint that Lean's kernel
  cannot carry inside the inductive type. -/

/-- A RecursiveSystem is well-formed iff at every composite level:
    - Every component in the system's composition is some child's thing
    - Every child's thing belongs to the system's composition
    - All children are themselves well-formed

    Process primitives are trivially well-formed. -/
def RecursiveSystem.WellFormed {α : Type*} [ActsOn α] :
    RecursiveSystem α → Prop
  | .primitive _ => True
  | .composite _ sys children =>
      (∀ x ∈ sys.composition, ∃ c ∈ children, c.thing = x) ∧
      (∀ c ∈ children, c.thing ∈ sys.composition) ∧
      (∀ c ∈ children, c.WellFormed)

/-! ## Organized vs. Aggregate -/

/-- A collection of things is organized iff it has nonempty internal bonds.
    This is the formal content of Mobus's "organized vs. heaped" distinction.

    An organized set has at least two distinct members that are bonded —
    there is genuine interaction, not just co-location. This predicate
    works on any set of things; ConcreteSystem.bondage_nonempty guarantees
    that every system's composition satisfies it. -/
def IsOrganized {α : Type*} [ActsOn α] (S : Set α) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ Bonded a b

/-- A collection is an aggregate iff it has no internal bonds.
    Mobus: an aggregate is "heaped" — components are co-located but
    do not interact. Assembly (Assembly.lean) is the transition from
    aggregate to organized. -/
def IsAggregate {α : Type*} [ActsOn α] (S : Set α) : Prop :=
  ¬IsOrganized S

/-- Every ConcreteSystem's composition is organized.
    Immediate from bondage_nonempty — the defining constraint
    that separates systems from mere collections. -/
theorem ConcreteSystem.composition_organized {α : Type*} [ActsOn α]
    (σ : ConcreteSystem α) : IsOrganized σ.composition := by
  obtain ⟨a, ha, b, hb, hne, hbond⟩ := σ.bondage_nonempty
  exact ⟨a, ha, b, hb, hne, hbond⟩

/-- An aggregate that gains bonds becomes organized.
    This connects to Assembly.lean: assembly is the process by which
    an aggregate becomes a system. -/
theorem organized_of_bond {α : Type*} [ActsOn α] {S : Set α}
    {a b : α} (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b)
    (hbond : Bonded a b) : IsOrganized S :=
  ⟨a, ha, b, hb, hne, hbond⟩

/-! ## Basic Properties -/

/-- A process primitive has depth 0. -/
theorem RecursiveSystem.primitive_depth {α : Type*} [ActsOn α] (a : α) :
    (RecursiveSystem.primitive a : RecursiveSystem α).depth = 0 := by
  unfold RecursiveSystem.depth
  rfl

/-- A process primitive counts as exactly 1. -/
theorem RecursiveSystem.primitive_count {α : Type*} [ActsOn α] (a : α) :
    (RecursiveSystem.primitive a : RecursiveSystem α).primitiveCount = 1 := by
  unfold RecursiveSystem.primitiveCount
  rfl

/-- Every node is either a primitive or composite. -/
theorem RecursiveSystem.primitive_or_composite {α : Type*} [ActsOn α]
    (rs : RecursiveSystem α) :
    rs.isPrimitive = true ∨ rs.isComposite = true := by
  cases rs with
  | primitive _ => exact Or.inl rfl
  | composite _ _ _ => exact Or.inr rfl

/-- A process primitive is well-formed. -/
theorem RecursiveSystem.primitive_wellFormed {α : Type*} [ActsOn α] (a : α) :
    (RecursiveSystem.primitive a : RecursiveSystem α).WellFormed := by
  unfold RecursiveSystem.WellFormed
  trivial

/-! ## Closure Under Decomposition

  The central Systemness theorem: the subsystems of a well-formed
  RecursiveSystem are themselves well-formed RecursiveSystems. This is
  the formal content of Mobus's claim that "every component is either
  atomic or itself a system."

  The theorem is structurally trivial — WellFormed propagates by
  definition. But the DESIGN made it trivial: by requiring ConcreteSystem
  at each composite level and WellFormed at each child, we built the
  closure property into the type + predicate. The theorem witnesses what
  the design guarantees. -/

/-- Well-formedness propagates to children: every child of a well-formed
    composite is itself well-formed.
    This is closure under decomposition — the defining property of
    Systemness as a principle. -/
theorem RecursiveSystem.child_wellFormed {α : Type*} [ActsOn α]
    {t : α} {sys : ConcreteSystem α}
    {children : List (RecursiveSystem α)}
    (hwf : (RecursiveSystem.composite t sys children).WellFormed)
    {child : RecursiveSystem α} (hmem : child ∈ children) :
    child.WellFormed := by
  unfold RecursiveSystem.WellFormed at hwf
  exact hwf.2.2 child hmem

/-- In a well-formed composite, every child's thing belongs to the
    parent's composition. -/
theorem RecursiveSystem.child_thing_in_composition {α : Type*} [ActsOn α]
    {t : α} {sys : ConcreteSystem α}
    {children : List (RecursiveSystem α)}
    (hwf : (RecursiveSystem.composite t sys children).WellFormed)
    {child : RecursiveSystem α} (hmem : child ∈ children) :
    child.thing ∈ sys.composition := by
  unfold RecursiveSystem.WellFormed at hwf
  exact hwf.2.1 child hmem

/-- In a well-formed composite, every component in the composition
    is represented by some child. -/
theorem RecursiveSystem.composition_covered {α : Type*} [ActsOn α]
    {t : α} {sys : ConcreteSystem α}
    {children : List (RecursiveSystem α)}
    (hwf : (RecursiveSystem.composite t sys children).WellFormed)
    {x : α} (hx : x ∈ sys.composition) :
    ∃ c ∈ children, c.thing = x := by
  unfold RecursiveSystem.WellFormed at hwf
  exact hwf.1 x hx

/-- The composition of every composite level is organized (not aggregate).
    Every composite node carries a ConcreteSystem, which by definition has
    nonempty bondage. Therefore no level in the decomposition tree is a
    mere aggregate — systemness holds at every level. -/
theorem RecursiveSystem.every_level_organized {α : Type*} [ActsOn α]
    (sys : ConcreteSystem α) :
    IsOrganized sys.composition :=
  sys.composition_organized

/-! ## Closure Under Composition

  The upward direction of Systemness: systems compose into supersystems.
  Mobus §2.3.1: "Systems interact with other systems, forming yet larger
  systems. The Universe is composed of systems of systems."

  Closure under decomposition (above) shows subsystems are systems.
  Closure under composition shows interacting systems form a system.
  Together they establish that the space of systems is closed in both
  directions — the defining property of Systemness as a principle.

  The construction takes two systems with disjoint compositions and at
  least one cross-boundary bond, and produces a supersystem. The
  environment of the composed system is the union of both environments
  minus anything that became a component — the unique minimal environment
  satisfying `structure_on`. -/

/-- Compose two interacting systems into a supersystem.

    Given σ₁ and σ₂ with disjoint compositions and at least one bond
    between their components, produce a ConcreteSystem whose composition
    is the union, whose environment is the minimal set satisfying
    structure_on, and whose structure combines both systems' relations.

    Mobus §2.3.1: "Systems interact with other systems, forming yet
    larger systems."

    The environment formula (E₁ ∪ E₂) \ (C₁ ∪ C₂) is the unique
    minimal environment: intersection would break structure_on
    (environmental things referenced by one system's structure but
    unknown to the other would have no home in C ∪ E).

    FINDING: Neither hypothesis is needed for the coherence proofs.
    The CES construction is unconditionally valid — any two systems
    can be combined. The hypotheses add physical content: disjointness
    ensures distinct systems, interaction ensures meaningful composition
    (not just disjoint union). -/
def ConcreteSystem.compose {α : Type*} [ActsOn α]
    (σ₁ σ₂ : ConcreteSystem α)
    (_h_disjoint : σ₁.composition ∩ σ₂.composition = ∅)
    (_h_interact : ∃ a ∈ σ₁.composition, ∃ b ∈ σ₂.composition, Bonded a b)
    : ConcreteSystem α where
  composition := σ₁.composition ∪ σ₂.composition
  environment := (σ₁.environment ∪ σ₂.environment) \ (σ₁.composition ∪ σ₂.composition)
  structure' := σ₁.structure' ∪ σ₂.structure'
  disjoint := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_union, Set.mem_empty_iff_false,
               iff_false]
    rintro ⟨hc, -, hnc⟩
    exact hnc hc
  structure_on := by
    intro p hp
    rcases hp with hp₁ | hp₂
    · obtain ⟨h1, h2⟩ := σ₁.structure_on p hp₁
      refine ⟨?_, ?_⟩
      · rcases h1 with hc | he
        · exact Or.inl (Or.inl hc)
        · by_cases hc2 : p.1 ∈ σ₂.composition
          · exact Or.inl (Or.inr hc2)
          · have hc1 : p.1 ∉ σ₁.composition :=
              fun h => Set.eq_empty_iff_forall_notMem.mp σ₁.disjoint p.1 ⟨h, he⟩
            exact Or.inr ⟨Or.inl he, fun hcu => hcu.elim hc1 hc2⟩
      · rcases h2 with hc | he
        · exact Or.inl (Or.inl hc)
        · by_cases hc2 : p.2 ∈ σ₂.composition
          · exact Or.inl (Or.inr hc2)
          · have hc1 : p.2 ∉ σ₁.composition :=
              fun h => Set.eq_empty_iff_forall_notMem.mp σ₁.disjoint p.2 ⟨h, he⟩
            exact Or.inr ⟨Or.inl he, fun hcu => hcu.elim hc1 hc2⟩
    · obtain ⟨h1, h2⟩ := σ₂.structure_on p hp₂
      refine ⟨?_, ?_⟩
      · rcases h1 with hc | he
        · exact Or.inl (Or.inr hc)
        · by_cases hc1 : p.1 ∈ σ₁.composition
          · exact Or.inl (Or.inl hc1)
          · have hc2 : p.1 ∉ σ₂.composition :=
              fun h => Set.eq_empty_iff_forall_notMem.mp σ₂.disjoint p.1 ⟨h, he⟩
            exact Or.inr ⟨Or.inr he, fun hcu => hcu.elim hc1 hc2⟩
      · rcases h2 with hc | he
        · exact Or.inl (Or.inr hc)
        · by_cases hc1 : p.2 ∈ σ₁.composition
          · exact Or.inl (Or.inl hc1)
          · have hc2 : p.2 ∉ σ₂.composition :=
              fun h => Set.eq_empty_iff_forall_notMem.mp σ₂.disjoint p.2 ⟨h, he⟩
            exact Or.inr ⟨Or.inr he, fun hcu => hcu.elim hc1 hc2⟩
  bondage_nonempty := by
    obtain ⟨a, ha, b, hb, hne, hbond⟩ := σ₁.bondage_nonempty
    exact ⟨a, Set.mem_union_left _ ha, b, Set.mem_union_left _ hb, hne, hbond⟩

/-- The composed system's composition contains σ₁'s composition. -/
theorem ConcreteSystem.compose_contains_left {α : Type*} [ActsOn α]
    {σ₁ σ₂ : ConcreteSystem α}
    (h_disjoint : σ₁.composition ∩ σ₂.composition = ∅)
    (h_interact : ∃ a ∈ σ₁.composition, ∃ b ∈ σ₂.composition, Bonded a b) :
    σ₁.composition ⊆ (σ₁.compose σ₂ h_disjoint h_interact).composition :=
  Set.subset_union_left

/-- The composed system's composition contains σ₂'s composition. -/
theorem ConcreteSystem.compose_contains_right {α : Type*} [ActsOn α]
    {σ₁ σ₂ : ConcreteSystem α}
    (h_disjoint : σ₁.composition ∩ σ₂.composition = ∅)
    (h_interact : ∃ a ∈ σ₁.composition, ∃ b ∈ σ₂.composition, Bonded a b) :
    σ₂.composition ⊆ (σ₁.compose σ₂ h_disjoint h_interact).composition :=
  Set.subset_union_right

/-- The composed system preserves σ₁'s structure. -/
theorem ConcreteSystem.compose_preserves_structure_left {α : Type*} [ActsOn α]
    {σ₁ σ₂ : ConcreteSystem α}
    (h_disjoint : σ₁.composition ∩ σ₂.composition = ∅)
    (h_interact : ∃ a ∈ σ₁.composition, ∃ b ∈ σ₂.composition, Bonded a b) :
    σ₁.structure' ⊆ (σ₁.compose σ₂ h_disjoint h_interact).structure' :=
  Set.subset_union_left

/-- The composed system preserves σ₂'s structure. -/
theorem ConcreteSystem.compose_preserves_structure_right {α : Type*} [ActsOn α]
    {σ₁ σ₂ : ConcreteSystem α}
    (h_disjoint : σ₁.composition ∩ σ₂.composition = ∅)
    (h_interact : ∃ a ∈ σ₁.composition, ∃ b ∈ σ₂.composition, Bonded a b) :
    σ₂.structure' ⊆ (σ₁.compose σ₂ h_disjoint h_interact).structure' :=
  Set.subset_union_right

/-- The composed system is organized. -/
theorem ConcreteSystem.compose_organized {α : Type*} [ActsOn α]
    (σ₁ σ₂ : ConcreteSystem α)
    (h_disjoint : σ₁.composition ∩ σ₂.composition = ∅)
    (h_interact : ∃ a ∈ σ₁.composition, ∃ b ∈ σ₂.composition, Bonded a b) :
    IsOrganized (σ₁.compose σ₂ h_disjoint h_interact).composition :=
  (σ₁.compose σ₂ h_disjoint h_interact).composition_organized

end Systems
