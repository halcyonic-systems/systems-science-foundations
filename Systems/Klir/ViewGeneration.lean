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
  - The Rosen view (1978, Def 2.9.1, added 2026-09-16) costs the most:
    Kernel.IsIndist — the dependency must be an EQUIVALENCE on things.
    "States stand in for things": Rosen's pair (S, F) carries no
    relation among its states except the one the observables induce,
    s₁ R_F s₂ iff every observable agrees on them (p. 54, S/R_F), and
    that relation is always symmetric. A kernel with a one-way
    dependency has no Rosen view at all (rosen_no_view_of_asymmetric).

  Each view fills its elaboration slots with the MINIMAL canonical
  witness (empty environment, no external flows, no interfaces, PUnit
  for the parametric slots). The views differ in what they add around
  the kernel; the kernel itself passes through untouched — that is the
  round-trip content.
-/

import Systems.Klir.KlirSystem
import Mathlib.Data.Real.Basic

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
  interfaces_carry_flow := interfacesCarryFlow_empty _

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

/-! ## The Rosen View

  Rosen 1978, Definition 2.9.1 (book p. 54): "A system (or formal
  system) shall consist of a pair (S, F), where S is a set and F is a
  family of real-valued mappings defined on S." The gloss: "To each
  formal system defined as above, we can uniquely associate a set of
  reduced states S/R_F" — two states are identified when no observable
  separates them (§2.2–2.3).

  DATA-LEVEL ENCODING. `states` is S; `observables` is F, a set of
  functions α → ℝ (Proposition 2, p. 26, fixes the codomain); "defined
  on S" is carried as `defined_on`: an observable vanishes off S — the
  walking arrow (F depends on S) materialised as a Prop, exactly as
  `Kernel.dep_on` materialises "R depends on T". `RosenSystem.indist`
  is Rosen's R_F, the ONLY relation on states the pair determines, and
  `RosenSystem.toKlir` projects (S, R_F) — Rosen's own construction, not
  ours. Real numbers enter only as the canonical witness {0, 1} ⊆ ℝ, as
  PUnit fills the Mobus parametric slots.

  COST: `Kernel.IsIndist`. R_F is an equivalence relation, so a kernel
  round-trips through its Rosen view only if its dependency already is
  one. Generation: the observables are the indicator functions of the
  dependency classes. Round trip: indist recovers dep exactly. What is
  lost is stated as a theorem, not a remark: every Rosen view projects
  to a SYMMETRIC relation (`RosenSystem.indist_symm`), so a kernel with
  a one-way dependency has no Rosen view whose projection matches
  (`rosen_no_view_of_asymmetric`). That is the precise content of
  "states stand in for things": a thing that depends on another without
  the converse is a relation Rosen's pair cannot carry. -/

/-- Rosen's formal system (S, F) at the data level. -/
structure RosenSystem (α : Type*) where
  /-- S: the set of states. -/
  states : Set α
  /-- F: the family of real-valued observables. -/
  observables : Set (α → ℝ)
  /-- "defined on S": an observable carries no value off S. The walking
      arrow, F depends on S, as a Prop. -/
  defined_on : ∀ f ∈ observables, ∀ x, x ∉ states → f x = 0

/-- Rosen's R_F: two states are indistinguishable when every observable
    agrees on them (the relation whose quotient is S/R_F, p. 54). -/
def RosenSystem.indist {α : Type*} (V : RosenSystem α) : Set (α × α) :=
  {p | p.1 ∈ V.states ∧ p.2 ∈ V.states ∧ ∀ f ∈ V.observables, f p.1 = f p.2}

/-- Rosen's own projection to (T, R): states, and the relation R_F. -/
def RosenSystem.toKlir {α : Type*} (V : RosenSystem α) : KlirSystem α where
  things := V.states
  relation := V.indist

/-- R_F is symmetric — the fact that bounds what a Rosen view can carry. -/
theorem RosenSystem.indist_symm {α : Type*} (V : RosenSystem α)
    {p : α × α} (hp : p ∈ V.indist) : (p.2, p.1) ∈ V.indist :=
  ⟨hp.2.1, hp.1, fun f hf => (hp.2.2 f hf).symm⟩

/-- The price of the Rosen view: the dependency is an equivalence
    relation on the things. -/
structure Kernel.IsIndist {α : Type*} (k : Kernel α) : Prop where
  refl : ∀ a ∈ k.things, (a, a) ∈ k.dep
  symm : ∀ p ∈ k.dep, (p.2, p.1) ∈ k.dep
  trans : ∀ a b c, (a, b) ∈ k.dep → (b, c) ∈ k.dep → (a, c) ∈ k.dep

open Classical in
/-- The indicator of a thing's dependency class: 1 on the things related
    to `a`, 0 elsewhere. The canonical real-valued witness. -/
noncomputable def Kernel.classIndicator {α : Type*} (k : Kernel α) (a : α) : α → ℝ :=
  fun x => if (x, a) ∈ k.dep then 1 else 0

theorem Kernel.classIndicator_eq_one {α : Type*} (k : Kernel α) {a x : α}
    (h : (x, a) ∈ k.dep) : k.classIndicator a x = 1 := by
  simp [Kernel.classIndicator, h]

theorem Kernel.classIndicator_eq_zero {α : Type*} (k : Kernel α) {a x : α}
    (h : (x, a) ∉ k.dep) : k.classIndicator a x = 0 := by
  simp [Kernel.classIndicator, h]

/-- Generate the Rosen view: the things as states, one observable per
    dependency class. -/
noncomputable def Kernel.toRosen {α : Type*} (k : Kernel α) (_h : k.IsIndist) :
    RosenSystem α where
  states := k.things
  observables := {f | ∃ a ∈ k.things, f = k.classIndicator a}
  defined_on := by
    rintro f ⟨a, -, rfl⟩ x hx
    apply k.classIndicator_eq_zero
    intro hxa
    exact hx (k.dep_on _ hxa).1

/-- R_F of the generated view is exactly the kernel's dependency. -/
theorem Kernel.toRosen_indist {α : Type*} (k : Kernel α) (h : k.IsIndist) :
    (k.toRosen h).indist = k.dep := by
  ext ⟨s, t⟩
  constructor
  · rintro ⟨hs, ht, hf⟩
    have h1 := hf (k.classIndicator s) ⟨s, hs, rfl⟩
    rw [k.classIndicator_eq_one (h.refl s hs)] at h1
    by_contra hst
    have := k.classIndicator_eq_zero (a := s) (x := t)
      (fun hts => hst (h.symm _ hts))
    simp only at h1 this
    rw [this] at h1
    exact one_ne_zero h1
  · intro hst
    refine ⟨(k.dep_on _ hst).1, (k.dep_on _ hst).2, ?_⟩
    rintro f ⟨a, -, rfl⟩
    by_cases hsa : (s, a) ∈ k.dep
    · have hta : (t, a) ∈ k.dep := h.trans t s a (h.symm _ hst) hsa
      rw [k.classIndicator_eq_one hsa, k.classIndicator_eq_one hta]
    · have hta : (t, a) ∉ k.dep := fun hta => hsa (h.trans s t a hst hta)
      rw [k.classIndicator_eq_zero hsa, k.classIndicator_eq_zero hta]

/-- Round trip (Rosen): the generated pair projects back, through Rosen's
    own S/R_F construction, to the kernel's (T, R). -/
theorem Kernel.toRosen_toKlir {α : Type*} (k : Kernel α) (h : k.IsIndist) :
    (k.toRosen h).toKlir = k.toKlir :=
  KlirSystem.ext rfl (k.toRosen_indist h)

/-- Faithfulness (Rosen): distinct kernels generate distinct Rosen views. -/
theorem Kernel.toRosen_injective {α : Type*}
    {k₁ k₂ : Kernel α} {h₁ : k₁.IsIndist} {h₂ : k₂.IsIndist}
    (h : k₁.toRosen h₁ = k₂.toRosen h₂) : k₁ = k₂ :=
  Kernel.toKlir_injective <| by
    rw [← Kernel.toRosen_toKlir k₁ h₁, ← Kernel.toRosen_toKlir k₂ h₂, h]

/-- WHAT THE ROSEN VIEW CANNOT CARRY. A kernel in which some thing depends
    on another without the converse has NO Rosen view at all: no pair
    (S, F) projects, through R_F, to its (T, R). The cost of the view is
    not a slot left empty but a relation with no home. -/
theorem rosen_no_view_of_asymmetric {α : Type*} (k : Kernel α)
    (hasym : ∃ p ∈ k.dep, (p.2, p.1) ∉ k.dep) :
    ∀ V : RosenSystem α, V.toKlir ≠ k.toKlir := by
  intro V hV
  obtain ⟨p, hp, hnp⟩ := hasym
  have hrel : V.indist = k.dep := congrArg KlirSystem.relation hV
  apply hnp
  rw [← hrel] at hp ⊢
  exact V.indist_symm hp

end Systems
