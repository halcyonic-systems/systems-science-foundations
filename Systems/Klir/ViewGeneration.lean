/-
  Systems/Klir/ViewGeneration.lean
  The K ≅ 2 kernel generates each tradition's presentation as a faithful view

  CommonCore.lean proves the convergence direction: the walking arrow
  embeds faithfully into all seven shape categories (the kernel sits
  INSIDE every tradition). KlirSystem.lean proves the projection
  direction: every tradition forgets down to (T, R).

  This file proves the CONSTRUCTION direction: from the kernel alone,
  each tradition's presentation is GENERATED as a derived view, and
  nothing is lost — projecting the generated view back yields the
  kernel unchanged (round-trip), and distinct kernels generate distinct
  views (faithfulness). Together: the traditions are views of one
  invariant, not independent ontologies that happen to agree.

  THE KERNEL AS DATA: KlirSystem's relation field is an unconstrained
  Set (α × α) — pairs need not lie in things. The K ≅ 2 arrow ("R
  depends on T") is exactly the missing constraint. The data-level
  kernel is therefore (T, R) PLUS the dependency proof: the walking
  arrow materializes as the Prop that KlirSystem omits.

  WHAT VIEW-GENERATION COSTS (findings):
  - The Klir view is free: Kernel ↔ dependency-constrained KlirSystem.
  - The Bunge view costs a bond: ConcreteSystem.bondage_nonempty forces
    the kernel to contain at least one bonded pair of distinct relata.
    Systemhood is not free — an empty or bond-free kernel generates no
    Bunge system.
  - The Mobus view costs irreflexivity: FlowNetwork.no_self_loops
    (Mobus §4.3, k ≠ o) forbids self-dependency. Klir and Bunge accept
    reflexive relations; the engineering view does not.

  Each view fills its elaboration slots with the MINIMAL canonical
  witness (empty environment, no external flows, no interfaces, PUnit
  for the parametric slots). The views differ in what they add around
  the kernel; the kernel itself passes through untouched — that is the
  round-trip content.
-/

import Systems.Klir.KlirSystem

namespace Systems

/-! ## The Kernel -/

/-- The K ≅ 2 kernel at the data level: a system IS a morphism.

    `things` and `dep` are Klir's (T, R); `dep_on` is the walking
    arrow — the structural commitment that relations depend on things.
    This Prop is what distinguishes the kernel from a bare KlirSystem,
    whose relation is unconstrained. -/
structure Kernel (α : Type*) where
  /-- T: the relata. -/
  things : Set α
  /-- R: the dependency relation — the morphism's graph. -/
  dep : Set (α × α)
  /-- The walking arrow: R is ON T. -/
  dep_on : ∀ p ∈ dep, p.1 ∈ things ∧ p.2 ∈ things

/-- Two kernels with the same things and dependency are equal
    (the arrow constraint is propositional). -/
theorem Kernel.ext {α : Type*} {k₁ k₂ : Kernel α}
    (ht : k₁.things = k₂.things) (hd : k₁.dep = k₂.dep) : k₁ = k₂ := by
  cases k₁; cases k₂
  simp_all

/-! ## The Klir View

  The Klir view is the forgetful image of the kernel: drop the arrow
  constraint, keep (T, R). Round trip: every KlirSystem that satisfies
  the dependency lifts back to the kernel uniquely. The Klir view is
  the kernel — Klir's (T, R) adds nothing and forgets only the
  constraint that makes it a system rather than a pair of sets. -/

/-- Generate the Klir view: forget the arrow, keep (T, R). -/
def Kernel.toKlir {α : Type*} (k : Kernel α) : KlirSystem α where
  things := k.things
  relation := k.dep

/-- Lift a dependency-respecting KlirSystem back to the kernel. -/
def KlirSystem.toKernel {α : Type*} (S : KlirSystem α)
    (h : ∀ p ∈ S.relation, p.1 ∈ S.things ∧ p.2 ∈ S.things) : Kernel α where
  things := S.things
  dep := S.relation
  dep_on := h

/-- Round trip (Klir): generating the view and lifting back is the identity. -/
theorem Kernel.toKlir_toKernel {α : Type*} (k : Kernel α) :
    k.toKlir.toKernel k.dep_on = k := rfl

/-- Round trip (Klir, other direction): lifting and regenerating is the identity. -/
theorem KlirSystem.toKernel_toKlir {α : Type*} (S : KlirSystem α)
    (h : ∀ p ∈ S.relation, p.1 ∈ S.things ∧ p.2 ∈ S.things) :
    (S.toKernel h).toKlir = S := rfl

/-- Faithfulness (Klir): distinct kernels generate distinct Klir views. -/
theorem Kernel.toKlir_injective {α : Type*} :
    Function.Injective (Kernel.toKlir (α := α)) := by
  intro k₁ k₂ h
  exact Kernel.ext (congrArg KlirSystem.things h) (congrArg KlirSystem.relation h)

/-! ## The Bunge View

  Generate the CES triple: composition = relata, environment = minimal
  (empty — the kernel makes no environmental commitment; environment is
  Bunge's elaboration), structure = the dependency. The generated view
  is a CLOSED system in Bunge's sense (Def 1.3: E = ∅).

  COST: ConcreteSystem.bondage_nonempty demands a bonded pair of
  distinct components. The kernel must already contain a bond. -/

/-- A kernel has a bond iff its dependency contains a pair of distinct,
    bonded relata. This is the price of the Bunge view: Def 1.1's
    bondage condition imposed back on the kernel. -/
def Kernel.HasBond {α : Type*} [ActsOn α] (k : Kernel α) : Prop :=
  ∃ p ∈ k.dep, p.1 ≠ p.2 ∧ Bonded p.1 p.2

/-- Generate the Bunge view: the kernel as a closed CES triple. -/
def Kernel.toBunge {α : Type*} [ActsOn α] (k : Kernel α) (hb : k.HasBond) :
    ConcreteSystem α where
  composition := k.things
  environment := ∅
  structure' := k.dep
  disjoint := Set.inter_empty _
  structure_on := fun p hp =>
    ⟨Or.inl (k.dep_on p hp).1, Or.inl (k.dep_on p hp).2⟩
  bondage_nonempty := by
    obtain ⟨p, hp, hne, hbond⟩ := hb
    exact ⟨p.1, (k.dep_on p hp).1, p.2, (k.dep_on p hp).2, hne, hbond⟩

/-- The generated Bunge view is closed: the kernel makes no
    environmental commitment, so the minimal view has E = ∅. -/
theorem Kernel.toBunge_isClosed {α : Type*} [ActsOn α]
    (k : Kernel α) (hb : k.HasBond) : (k.toBunge hb).isClosed := rfl

/-- Round trip (Bunge): the generated view projects back to the kernel's
    (T, R) — Bunge's elaboration adds environment but loses nothing. -/
theorem Kernel.toBunge_toKlir {α : Type*} [ActsOn α]
    (k : Kernel α) (hb : k.HasBond) :
    (k.toBunge hb).toKlir = k.toKlir := rfl

/-- Faithfulness (Bunge): distinct kernels generate distinct Bunge views. -/
theorem Kernel.toBunge_injective {α : Type*} [ActsOn α]
    {k₁ k₂ : Kernel α} {h₁ : k₁.HasBond} {h₂ : k₂.HasBond}
    (h : k₁.toBunge h₁ = k₂.toBunge h₂) : k₁ = k₂ :=
  Kernel.toKlir_injective <| by
    rw [← Kernel.toBunge_toKlir k₁ h₁, ← Kernel.toBunge_toKlir k₂ h₂, h]

/-! ## The Mobus View

  Generate the 8-tuple: components = relata, internal network = the
  dependency as a flow network, all other slots minimal (empty
  environment, no external flows, no interfaces, PUnit for the
  parametric slots κ μ π τ η δ — capacity, milieu, boundary
  properties, transforms, history, time scale).

  COST: FlowNetwork.no_self_loops (Mobus §4.3: k ≠ o) demands an
  irreflexive dependency. The engineering view forbids
  self-dependency that Klir and Bunge tolerate. -/

/-- A kernel is irreflexive iff no thing depends on itself.
    The price of the Mobus view. -/
def Kernel.Irreflexive {α : Type*} (k : Kernel α) : Prop :=
  ∀ p ∈ k.dep, p.1 ≠ p.2

/-- The kernel's dependency as a flow network: nodes = things,
    edges = dependency pairs with trivial capacity. -/
def Kernel.toFlowNetwork {α : Type*} (k : Kernel α) (hi : k.Irreflexive) :
    FlowNetwork α PUnit where
  nodes := k.things
  edges := {e | e.toPair ∈ k.dep}
  edges_on := fun e he => k.dep_on e.toPair he
  no_self_loops := fun e he => hi e.toPair he

/-- The empty flow network: no nodes, no edges. The minimal witness
    for the external-flow slot of a generated Mobus view. -/
def FlowNetwork.empty (α : Type*) (κ : Type*) : FlowNetwork α κ where
  nodes := ∅
  edges := ∅
  edges_on := fun e he => absurd he (Set.notMem_empty e)
  no_self_loops := fun e he => absurd he (Set.notMem_empty e)

/-- The empty network's relation is empty. -/
theorem FlowNetwork.empty_toRelation {α κ : Type*} :
    (FlowNetwork.empty α κ).toRelation = ∅ := by
  ext p
  simp [FlowNetwork.toRelation, FlowNetwork.empty]

/-- The generated network's relation is exactly the kernel's dependency:
    flows recover R with nothing added and nothing lost. -/
theorem Kernel.toFlowNetwork_toRelation {α : Type*}
    (k : Kernel α) (hi : k.Irreflexive) :
    (k.toFlowNetwork hi).toRelation = k.dep := by
  ext p
  constructor
  · rintro ⟨e, he, rfl⟩
    exact he
  · intro hp
    exact ⟨⟨p.1, p.2, PUnit.unit⟩, hp, rfl⟩

/-- Generate the Mobus view: the kernel as an 8-tuple with minimal
    elaboration slots. -/
def Kernel.toMobus {α : Type*} (k : Kernel α) (hi : k.Irreflexive) :
    MobusSystem α PUnit PUnit PUnit PUnit PUnit PUnit where
  components := k.things
  internalNetwork := k.toFlowNetwork hi
  environment := ⟨∅, PUnit.unit⟩
  externalFlows := FlowNetwork.empty α PUnit
  boundary := ⟨PUnit.unit, ∅⟩
  transforms := PUnit.unit
  history := PUnit.unit
  timeScale := PUnit.unit
  network_components := rfl
  disjoint := Set.inter_empty _
  interfaces_sub := Set.empty_subset _
  bipartite := fun e he => absurd he (Set.notMem_empty e)
  externalFlows_nodes := Set.empty_subset _

/-- The generated 8-tuple's total relation is exactly the kernel's
    dependency: internal flows recover R, external flows are empty. -/
theorem Kernel.toMobus_totalRelation {α : Type*}
    (k : Kernel α) (hi : k.Irreflexive) :
    (k.toMobus hi).totalRelation = k.dep := by
  unfold MobusSystem.totalRelation
  rw [show (k.toMobus hi).internalNetwork = k.toFlowNetwork hi from rfl,
      show (k.toMobus hi).externalFlows = FlowNetwork.empty α PUnit from rfl,
      Kernel.toFlowNetwork_toRelation, FlowNetwork.empty_toRelation,
      Set.union_empty]

/-- Round trip (Mobus): the generated 8-tuple projects back to the
    kernel's (T, R) — the six engineering elaborations add slots but
    lose nothing of the kernel. -/
theorem Kernel.toMobus_toKlir {α : Type*}
    (k : Kernel α) (hi : k.Irreflexive) :
    (k.toMobus hi).toKlir = k.toKlir :=
  KlirSystem.ext rfl (k.toMobus_totalRelation hi)

/-- Faithfulness (Mobus): distinct kernels generate distinct 8-tuples. -/
theorem Kernel.toMobus_injective {α : Type*}
    {k₁ k₂ : Kernel α} {h₁ : k₁.Irreflexive} {h₂ : k₂.Irreflexive}
    (h : k₁.toMobus h₁ = k₂.toMobus h₂) : k₁ = k₂ :=
  Kernel.toKlir_injective <| by
    rw [← Kernel.toMobus_toKlir k₁ h₁, ← Kernel.toMobus_toKlir k₂ h₂, h]

/-! ## View Coherence

  The generated views agree with each other, not just with the kernel:
  projecting the generated Mobus view down to Bunge (along the existing
  bridge) yields exactly the generated Bunge view. The commuting
  triangle of KlirSystem.lean extends to a commuting square with the
  kernel at the apex — the views are one structure seen three ways. -/

/-- A kernel's dependency induces action: every dependent pair is an
    action pair. Required to run the existing Mobus → Bunge bridge on
    a generated view. -/
def Kernel.DepActs {α : Type*} [ActsOn α] (k : Kernel α) : Prop :=
  ∀ p ∈ k.dep, actsOn p.1 p.2

/-- The generated flow network induces action when the kernel's
    dependency does. -/
theorem Kernel.toFlowNetwork_inducesAction {α : Type*} [ActsOn α]
    (k : Kernel α) (hi : k.Irreflexive) (ha : k.DepActs) :
    FlowInducesAction (k.toFlowNetwork hi) :=
  fun e he => ha e.toPair he

/-- A bonded kernel's generated network has at least one edge. -/
theorem Kernel.toFlowNetwork_edges_nonempty {α : Type*} [ActsOn α]
    (k : Kernel α) (hi : k.Irreflexive) (hb : k.HasBond) :
    (k.toFlowNetwork hi).edges.Nonempty := by
  obtain ⟨p, hp, -, -⟩ := hb
  exact ⟨⟨p.1, p.2, PUnit.unit⟩, hp⟩

/-- Two concrete systems with the same C, E, S are equal
    (the coherence constraints are propositional). -/
theorem ConcreteSystem.ext' {α : Type*} [ActsOn α] {σ₁ σ₂ : ConcreteSystem α}
    (hc : σ₁.composition = σ₂.composition)
    (he : σ₁.environment = σ₂.environment)
    (hs : σ₁.structure' = σ₂.structure') : σ₁ = σ₂ := by
  cases σ₁; cases σ₂
  simp_all

/-- VIEW COHERENCE: generating Mobus and projecting to Bunge equals
    generating Bunge directly. The kernel sits at the apex of the
    commuting triangle: every path between views fixes the kernel. -/
theorem Kernel.toMobus_toBunge {α : Type*} [ActsOn α]
    (k : Kernel α) (hi : k.Irreflexive) (hb : k.HasBond) (ha : k.DepActs) :
    (k.toMobus hi).toBunge (k.toFlowNetwork_inducesAction hi ha)
      (k.toFlowNetwork_edges_nonempty hi hb) = k.toBunge hb :=
  ConcreteSystem.ext' rfl rfl (k.toMobus_totalRelation hi)

end Systems
