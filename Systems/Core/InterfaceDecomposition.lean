/-
  Systems/Core/InterfaceDecomposition.lean
  Decomposing a BOUNDARY component — the membrane-crossing seam (SSF #43)

  `Systems/Core/Decomposition.lean` covers decomposing a component whose flows
  are all INTERIOR to the parent: `βsrc : childSources ≃ inflows(c)` and
  `βsnk : childSinks ≃ outflows(c)`, read off the parent's internal network `N`.
  It says nothing about `G` — so a component that is itself a parent interface,
  with flows crossing the membrane through it, falls outside that contract.
  bert-core transcribes the contract faithfully and therefore refuses such a
  component outright (`decomposability`, the "v1 interface-component refusal").

  This module states the contract for that case. `InterfaceDecomposition` is a
  SIBLING of `Decomposition`, not an extension: the interior bijections there
  range over ALL of `childSources`/`childSinks`, which is wrong once some of the
  child's boundary flows are membrane crossings rather than interior couplings.
  Here the child's boundary flows are PARTITIONED by whether their environmental
  endpoint is an object of the PARENT's environment:

    * interior half — the environmental endpoint is a stand-in for a parent
      interior neighbour of `comp`; treated exactly as in `Decomposition`
      (`βsrc`, `βsnk` against `inflows`/`outflows`);
    * crossing half — the environmental endpoint IS a parent environmental
      object; matched against the parent's EXO flows at `comp` (`γsrc`, `γsnk`
      against `exoInflows`/`exoOutflows`).

  The partition is a theorem, not a field (`childSources_partition`,
  `interior_crossing_src_disjoint`), because the parent's `disjoint` constraint
  already separates its components from its environmental objects.

  WHAT THE CROSSING HALF ADDS beyond a second pair of bijections:

    (a) direction preservation, by construction — `γsrc` bijects the child's
        crossing INBOUND flows with the parent inflows at `comp` (a receiver-side
        landing), `γsnk` the outbound with the parent outflows (an exporter-side
        origin). A crossing cannot satisfy the contract against the wrong half.
    (b) substance-kind preservation (`xsrc_preserves_kind`, `xsnk_preserves_kind`).
    (c) ENVIRONMENTAL-ENDPOINT preservation (`xsrc_env_preserved`,
        `xsnk_env_preserved`) — the child crossing runs to/from the very same
        environmental object as the parent crossing. This is the formal content
        of "the child's boundary REFINES the parent's crossing rather than
        ABSORBING it": the crossing is not re-terminated at a stand-in for
        `comp`; the same external counterparty now couples to a named child
        interface member (`src_lands`/`snk_lands`).

  NARROWING (recorded honestly, per SSF #35 and the repo's claim hygiene):

    * The refinement is ONE-TO-ONE. `γsrc`/`γsnk` are equivalences, so a single
      parent crossing may not fan out into two child crossings, nor two parent
      crossings merge into one. The Fed Balance Sheet case (bert-lenses #306)
      satisfies this — each authored flow lands on exactly one protocol-level
      mechanism — but a splitting refinement is NOT covered here and would need
      the bijections weakened to kind- and endpoint-preserving surjections with
      a conservation side-condition. Not attempted.
    * Structural only. No claim about `T` composition or `Δt`, exactly as in
      `Decomposition`. "Preserves the parent's environment couplings" means the
      endpoints and kinds are preserved, NOT that flow magnitudes balance —
      capacity is untouched.
    * Nothing here is proven about arbitrary depth or about verdict preservation
      across levels; those remain the conjectures recorded in `Decomposition.lean`.
-/

import Systems.Core.Decomposition
import Mathlib.Logic.Equiv.Set

namespace Systems

variable {α : Type*} {κ μ π τ η δ σ : Type*}

/-! ## Parent EXO flows at a component

  `inflows`/`outflows` (Decomposition.lean) read the parent's INTERNAL network
  `N`. These two read the parent's EXTERNAL flow network `G` at the same
  component — the membrane crossings the interior contract cannot see. By the
  parent's `bipartite` constraint they exist only when `comp` is an interface. -/

/-- `exoIn(c)`: parent external-flow edges crossing the membrane INTO `c`.
    The source of such an edge is an environmental object, so `c` is acting as
    a RECEIVER-side interface for it. -/
def exoInflows (S : MobusSystem α κ μ π τ η δ) (c : α) : Set (FlowEdge α κ) :=
  {e | e ∈ S.externalFlows.edges ∧ e.target = c}

/-- `exoOut(c)`: parent external-flow edges crossing the membrane OUT of `c`.
    `c` is acting as an EXPORTER-side interface. -/
def exoOutflows (S : MobusSystem α κ μ π τ η δ) (c : α) : Set (FlowEdge α κ) :=
  {e | e ∈ S.externalFlows.edges ∧ e.source = c}

/-! ## Splitting the child's boundary flows

  The child's environment `E′` mixes two populations: stand-ins for the parent's
  interior neighbours of `comp`, and genuine objects of the PARENT's environment
  that used to couple to `comp` across the membrane. `O` below is always
  instantiated at `parent.environment.objects`. -/

/-- Child boundary INFLOWS whose environmental origin is a parent environmental
    object: the child-side halves of the parent's membrane crossings into `comp`. -/
def crossingSources (child : MobusSystem α κ μ π τ η δ) (O : Set α) :
    Set (FlowEdge α κ) :=
  {e | e ∈ childSources child ∧ e.source ∈ O}

/-- Child boundary OUTFLOWS whose environmental destination is a parent
    environmental object: the child-side halves of the crossings out of `comp`. -/
def crossingSinks (child : MobusSystem α κ μ π τ η δ) (O : Set α) :
    Set (FlowEdge α κ) :=
  {e | e ∈ childSinks child ∧ e.target ∈ O}

/-- Child boundary inflows from an interior stand-in — the `Decomposition` case. -/
def interiorSources (child : MobusSystem α κ μ π τ η δ) (O : Set α) :
    Set (FlowEdge α κ) :=
  {e | e ∈ childSources child ∧ e.source ∉ O}

/-- Child boundary outflows to an interior stand-in — the `Decomposition` case. -/
def interiorSinks (child : MobusSystem α κ μ π τ η δ) (O : Set α) :
    Set (FlowEdge α κ) :=
  {e | e ∈ childSinks child ∧ e.target ∉ O}

/-! ### The split is a partition (theorem, not a field) -/

/-- The child's boundary inflows split exactly into interior and crossing. -/
theorem childSources_partition (child : MobusSystem α κ μ π τ η δ) (O : Set α)
    [DecidablePred (· ∈ O)] :
    childSources child = interiorSources child O ∪ crossingSources child O := by
  ext e
  constructor
  · intro he
    by_cases h : e.source ∈ O
    · exact Or.inr ⟨he, h⟩
    · exact Or.inl ⟨he, h⟩
  · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he

/-- The child's boundary outflows split exactly into interior and crossing. -/
theorem childSinks_partition (child : MobusSystem α κ μ π τ η δ) (O : Set α)
    [DecidablePred (· ∈ O)] :
    childSinks child = interiorSinks child O ∪ crossingSinks child O := by
  ext e
  constructor
  · intro he
    by_cases h : e.target ∈ O
    · exact Or.inr ⟨he, h⟩
    · exact Or.inl ⟨he, h⟩
  · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he

/-- Nothing is counted twice on the inflow side. -/
theorem interior_crossing_src_disjoint (child : MobusSystem α κ μ π τ η δ) (O : Set α) :
    interiorSources child O ∩ crossingSources child O = ∅ := by
  ext e
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨_, hno⟩, ⟨_, hyes⟩⟩
  exact hno hyes

/-- Nothing is counted twice on the outflow side. -/
theorem interior_crossing_snk_disjoint (child : MobusSystem α κ μ π τ η δ) (O : Set α) :
    interiorSinks child O ∩ crossingSinks child O = ∅ := by
  ext e
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨_, hno⟩, ⟨_, hyes⟩⟩
  exact hno hyes

/-! ## The interface-decomposition structure -/

/-- A decomposition of a component `comp` that is itself an INTERFACE of
    `parent` — flows cross the parent's membrane through it.

    Fields `βsrc`/`βsnk` are the `Decomposition` contract restricted to the
    interior half of the child's boundary; `γsrc`/`γsnk` are the new content,
    carrying the parent's membrane crossings at `comp` into the child's own
    boundary. `derived_env` widens `Decomposition.derived_env` by exactly the
    external neighbourhood of `comp` — the environmental objects the crossings
    connect to must appear in `E′`, and nothing else may.

    As in `Decomposition`, `kind` is an explicit substance labelling because
    `FlowEdge` carries no substance slot, and `T′`/`H′`/`Δt′` do not appear. -/
structure InterfaceDecomposition (α κ μ π τ η δ σ : Type*) where
  /-- The parent flat 8-tuple (one level). -/
  parent : MobusSystem α κ μ π τ η δ
  /-- The boundary component being decomposed. -/
  comp : α
  /-- The child flat 8-tuple that replaces `comp`'s opacity. -/
  child : MobusSystem α κ μ π τ η δ
  /-- Substance-kind label on flow edges (matter / energy / message). -/
  kind : FlowEdge α κ → σ
  /-- The decomposed component is a genuine parent component. -/
  comp_mem : comp ∈ parent.components
  /-- …and it is a parent INTERFACE. This is what `Decomposition` excludes. -/
  comp_interface : comp ∈ parent.boundary.interfaces
  /-- Interior contract, source half — unchanged from `Decomposition`. -/
  βsrc : interiorSources child parent.environment.objects ≃ inflows parent comp
  /-- Interior contract, sink half — unchanged from `Decomposition`. -/
  βsnk : interiorSinks child parent.environment.objects ≃ outflows parent comp
  /-- CROSSING contract, receiver half: child crossing inflows biject with the
      parent's exo inflows at `comp`. Direction is preserved by construction. -/
  γsrc : crossingSources child parent.environment.objects ≃ exoInflows parent comp
  /-- CROSSING contract, exporter half: child crossing outflows biject with the
      parent's exo outflows at `comp`. -/
  γsnk : crossingSinks child parent.environment.objects ≃ exoOutflows parent comp
  /-- `βsrc` preserves substance kind. -/
  src_preserves_kind : ∀ e : interiorSources child parent.environment.objects,
    kind (↑(βsrc e) : FlowEdge α κ) = kind (↑e : FlowEdge α κ)
  /-- `βsnk` preserves substance kind. -/
  snk_preserves_kind : ∀ e : interiorSinks child parent.environment.objects,
    kind (↑(βsnk e) : FlowEdge α κ) = kind (↑e : FlowEdge α κ)
  /-- `γsrc` preserves substance kind: a crossing may not be re-kinded on the
      way through the finer boundary. -/
  xsrc_preserves_kind : ∀ e : crossingSources child parent.environment.objects,
    kind (↑(γsrc e) : FlowEdge α κ) = kind (↑e : FlowEdge α κ)
  /-- `γsnk` preserves substance kind. -/
  xsnk_preserves_kind : ∀ e : crossingSinks child parent.environment.objects,
    kind (↑(γsnk e) : FlowEdge α κ) = kind (↑e : FlowEdge α κ)
  /-- REFINE, DON'T ABSORB (receiver half): the child crossing originates at the
      very same environmental object as the parent crossing it answers for. -/
  xsrc_env_preserved : ∀ e : crossingSources child parent.environment.objects,
    (↑(γsrc e) : FlowEdge α κ).source = (↑e : FlowEdge α κ).source
  /-- REFINE, DON'T ABSORB (exporter half): same environmental destination. -/
  xsnk_env_preserved : ∀ e : crossingSinks child parent.environment.objects,
    (↑(γsnk e) : FlowEdge α κ).target = (↑e : FlowEdge α κ).target
  /-- Every child boundary inflow — interior or crossing — lands on a child
      interface member. This is what makes the crossing land somewhere NAMED. -/
  src_lands : ∀ e ∈ childSources child, e.target ∈ child.boundary.interfaces
  /-- Every child boundary outflow leaves from a child interface member. -/
  snk_lands : ∀ e ∈ childSinks child, e.source ∈ child.boundary.interfaces
  /-- `E′` is DERIVED: the parent's interior neighbourhood of `comp` (as in
      `Decomposition`) TOGETHER WITH its external neighbourhood — the
      environmental objects on the far side of its membrane crossings.
      Nothing else may appear in `E′`. -/
  derived_env : child.environment.objects =
    (parent.internalNetwork.successors comp ∪ parent.internalNetwork.predecessors comp)
      ∪ (parent.externalFlows.successors comp ∪ parent.externalFlows.predecessors comp)

namespace InterfaceDecomposition

variable (d : InterfaceDecomposition α κ μ π τ η δ σ)

/-- Shorthand for the parent's environmental objects, the set the child's
    boundary flows are partitioned against. -/
abbrev envO : Set α := d.parent.environment.objects

/-! ## The two seams -/

/-- The interior seam — literally `Decomposition.seam`, restricted to the
    interior half of the child's boundary. -/
def interiorSeam :
    (interiorSources d.child d.envO ⊕ interiorSinks d.child d.envO) ≃
      (inflows d.parent d.comp ⊕ outflows d.parent d.comp) :=
  Equiv.sumCongr d.βsrc d.βsnk

/-- The CROSSING seam: the child's membrane-crossing boundary flows against the
    parent's exo flows at `comp`. -/
def crossingSeam :
    (crossingSources d.child d.envO ⊕ crossingSinks d.child d.envO) ≃
      (exoInflows d.parent d.comp ⊕ exoOutflows d.parent d.comp) :=
  Equiv.sumCongr d.γsrc d.γsnk

/-- The full seam: every boundary flow of the child, against every flow of the
    parent at `comp` — interior and membrane-crossing together. -/
def fullSeam :
    ((interiorSources d.child d.envO ⊕ interiorSinks d.child d.envO) ⊕
      (crossingSources d.child d.envO ⊕ crossingSinks d.child d.envO)) ≃
    ((inflows d.parent d.comp ⊕ outflows d.parent d.comp) ⊕
      (exoInflows d.parent d.comp ⊕ exoOutflows d.parent d.comp)) :=
  Equiv.sumCongr d.interiorSeam d.crossingSeam

/-! ### Direction preservation, by construction -/

@[simp] theorem interiorSeam_inl (e : interiorSources d.child d.envO) :
    d.interiorSeam (Sum.inl e) = Sum.inl (d.βsrc e) := rfl

@[simp] theorem interiorSeam_inr (e : interiorSinks d.child d.envO) :
    d.interiorSeam (Sum.inr e) = Sum.inr (d.βsnk e) := rfl

@[simp] theorem crossingSeam_inl (e : crossingSources d.child d.envO) :
    d.crossingSeam (Sum.inl e) = Sum.inl (d.γsrc e) := rfl

@[simp] theorem crossingSeam_inr (e : crossingSinks d.child d.envO) :
    d.crossingSeam (Sum.inr e) = Sum.inr (d.γsnk e) := rfl

@[simp] theorem fullSeam_interior (x) :
    d.fullSeam (Sum.inl x) = Sum.inl (d.interiorSeam x) := rfl

@[simp] theorem fullSeam_crossing (x) :
    d.fullSeam (Sum.inr x) = Sum.inr (d.crossingSeam x) := rfl

/-! ### Flow conservation at the seam -/

/-- Each parent membrane crossing INTO `comp` continues into exactly one child
    crossing inflow. -/
theorem exoInflow_continues (p : exoInflows d.parent d.comp) :
    ∃! e : crossingSources d.child d.envO, d.γsrc e = p :=
  d.γsrc.bijective.existsUnique p

/-- Each parent membrane crossing OUT of `comp` continues into exactly one
    child crossing outflow. -/
theorem exoOutflow_continues (p : exoOutflows d.parent d.comp) :
    ∃! e : crossingSinks d.child d.envO, d.γsnk e = p :=
  d.γsnk.bijective.existsUnique p

/-- The full seam is a bijection: nothing at `comp` is dropped or invented. -/
theorem fullSeam_bijective : Function.Bijective d.fullSeam :=
  d.fullSeam.bijective

/-! ## Refine, don't absorb -/

/-- The underlying flow edge of a boundary-flow element on either side. -/
private def edgeOf {A B : Set (FlowEdge α κ)} : A ⊕ B → FlowEdge α κ :=
  Sum.elim (fun e => ↑e) (fun e => ↑e)

/-- The underlying flow edge across the four-way seam. -/
private def edgeOf₄ {A B C D : Set (FlowEdge α κ)} :
    (A ⊕ B) ⊕ (C ⊕ D) → FlowEdge α κ :=
  Sum.elim edgeOf edgeOf

/-- Substance kind is preserved across the whole four-way seam. -/
theorem fullSeam_preserves_kind (x) :
    d.kind (edgeOf₄ (d.fullSeam x)) = d.kind (edgeOf₄ x) := by
  cases x with
  | inl y =>
    cases y with
    | inl e => exact d.src_preserves_kind e
    | inr e => exact d.snk_preserves_kind e
  | inr y =>
    cases y with
    | inl e => exact d.xsrc_preserves_kind e
    | inr e => exact d.xsnk_preserves_kind e

/-- **Refinement, receiver half.** Every parent membrane crossing into `comp` is
    carried by exactly one child boundary flow, and that flow (i) comes from the
    SAME environmental object, (ii) carries the SAME substance kind, and
    (iii) terminates on a NAMED child interface member. The parent's coupling to
    its environment survives the decomposition intact, now resolved to a
    finer-grained interface. -/
theorem crossing_refines_inflow (p : exoInflows d.parent d.comp) :
    ∃! e : crossingSources d.child d.envO,
      d.γsrc e = p ∧
      (↑e : FlowEdge α κ).source = (↑p : FlowEdge α κ).source ∧
      d.kind (↑e : FlowEdge α κ) = d.kind (↑p : FlowEdge α κ) ∧
      (↑e : FlowEdge α κ).target ∈ d.child.boundary.interfaces := by
  refine ⟨d.γsrc.symm p, ⟨d.γsrc.apply_symm_apply p, ?_, ?_, ?_⟩, ?_⟩
  · have := d.xsrc_env_preserved (d.γsrc.symm p)
    rw [d.γsrc.apply_symm_apply p] at this
    exact this.symm
  · have := d.xsrc_preserves_kind (d.γsrc.symm p)
    rw [d.γsrc.apply_symm_apply p] at this
    exact this.symm
  · exact d.src_lands _ (d.γsrc.symm p).2.1
  · rintro e ⟨he, -, -, -⟩
    rw [← he, d.γsrc.symm_apply_apply]

/-- **Refinement, exporter half.** Same statement for crossings out of `comp`:
    same environmental destination, same substance kind, originating at a named
    child interface member. -/
theorem crossing_refines_outflow (p : exoOutflows d.parent d.comp) :
    ∃! e : crossingSinks d.child d.envO,
      d.γsnk e = p ∧
      (↑e : FlowEdge α κ).target = (↑p : FlowEdge α κ).target ∧
      d.kind (↑e : FlowEdge α κ) = d.kind (↑p : FlowEdge α κ) ∧
      (↑e : FlowEdge α κ).source ∈ d.child.boundary.interfaces := by
  refine ⟨d.γsnk.symm p, ⟨d.γsnk.apply_symm_apply p, ?_, ?_, ?_⟩, ?_⟩
  · have := d.xsnk_env_preserved (d.γsnk.symm p)
    rw [d.γsnk.apply_symm_apply p] at this
    exact this.symm
  · have := d.xsnk_preserves_kind (d.γsnk.symm p)
    rw [d.γsnk.apply_symm_apply p] at this
    exact this.symm
  · exact d.snk_lands _ (d.γsnk.symm p).2.1
  · rintro e ⟨he, -, -, -⟩
    rw [← he, d.γsnk.symm_apply_apply]

/-- The crossing half never absorbs a coupling into the child's interior: every
    environmental object the parent couples to through `comp` still appears in
    the child's environment, by `derived_env`. -/
theorem exo_partner_in_child_env {e : FlowEdge α κ}
    (he : e ∈ exoInflows d.parent d.comp) :
    e.source ∈ d.child.environment.objects := by
  rw [d.derived_env]
  exact Or.inr (Or.inr ⟨e, he.1, rfl, he.2⟩)

/-- Same, on the exporter side. -/
theorem exo_partner_in_child_env' {e : FlowEdge α κ}
    (he : e ∈ exoOutflows d.parent d.comp) :
    e.target ∈ d.child.environment.objects := by
  rw [d.derived_env]
  exact Or.inr (Or.inl ⟨e, he.1, he.2, rfl⟩)

/-! ## Substitution soundness (structural) -/

/-- **Substitution soundness for a boundary component.** Substituting the
    contracted child for the interface `comp` preserves:

    1. every flow at `comp`, interior and membrane-crossing — the full seam is a
       bijection, so nothing is dropped and nothing is invented;
    2. flow direction, by construction (`inl`/`inr` blocks are preserved, and
       the interior/crossing split is preserved);
    3. substance kind, across all four halves;
    4. **the parent's environment couplings** — each crossing keeps its
       environmental counterparty and lands on a named child interface member.

    Purely structural, exactly as `Decomposition.substitution_sound`: no `T`
    composition, no `Δt`, no claim about flow magnitudes (capacity is untouched).
    Point 4 is the content that the interior contract cannot state. -/
theorem substitution_sound :
    Function.Bijective d.fullSeam ∧
      (∀ x, d.fullSeam (Sum.inl x) = Sum.inl (d.interiorSeam x)) ∧
      (∀ x, d.fullSeam (Sum.inr x) = Sum.inr (d.crossingSeam x)) ∧
      (∀ x, d.kind (edgeOf₄ (d.fullSeam x)) = d.kind (edgeOf₄ x)) ∧
      (∀ e : crossingSources d.child d.envO,
        (↑(d.γsrc e) : FlowEdge α κ).source = (↑e : FlowEdge α κ).source) ∧
      (∀ e : crossingSinks d.child d.envO,
        (↑(d.γsnk e) : FlowEdge α κ).target = (↑e : FlowEdge α κ).target) ∧
      (∀ e ∈ childSources d.child, e.target ∈ d.child.boundary.interfaces) ∧
      (∀ e ∈ childSinks d.child, e.source ∈ d.child.boundary.interfaces) :=
  ⟨d.fullSeam.bijective, fun _ => rfl, fun _ => rfl, d.fullSeam_preserves_kind,
   d.xsrc_env_preserved, d.xsnk_env_preserved, d.src_lands, d.snk_lands⟩

end InterfaceDecomposition

/-! ## Non-vacuity: the crossing contract refuses things (SSF #35)

  A constraint that nothing can fail proves nothing. This section pays the
  separating-instance debt for `InterfaceDecomposition` with three concrete
  models over the same parent — one that satisfies the contract and two that
  provably cannot.

  THE PARENT is a toy Federal Reserve level (the shape of bert-lenses #306, cut
  to three flows). Its components are a Balance Sheet (`10`) and an Open Market
  Desk (`11`); its environment holds the Treasury (`20`) and the Banks (`21`).
  The Balance Sheet is the parent's one INTERFACE: it receives from the Treasury
  and exports to the Banks, so two of the parent's three flows cross the
  membrane through it. `Decomposition` cannot be applied to it at all — this is
  exactly the component bert-core's v1 gate refuses.

  THE PASSING CHILD (`fedSplit`) decomposes the Balance Sheet into two
  protocol-level mechanisms: a TGA account (`30`) that receives the Treasury
  crossing, and reserve accounts (`31`) that export the Banks crossing. The
  interior message flow from the Desk lands on the TGA account. Both mechanisms
  are child interface members, so each parent crossing is now carried by a NAMED
  finer component with its counterparty and substance tag intact.

  THE FAILING CHILDREN:
  * `droppedChild` — the Treasury crossing is absorbed rather than refined: the
    child still declares the Treasury in `E′` but no child boundary flow
    receives from it. No `γsrc` can exist (`crossing_dropped_refused`).
  * `childWith 9` — the Treasury crossing survives but is re-kinded on the way
    through the finer boundary (`rekind_refused`).

  DOES NOT COUNT (pre-registered, following `Interface.lean`'s precedent):
  - a degenerate parent with no membrane crossings, which would leave open
    whether the contract only bites when nothing crosses — the parent below has
    two live crossings and a live interior flow;
  - an added hypothesis that assumes part of the claim;
  - a new axiom bridging the gap.

  SCOPE OF THE RE-KINDING REFUSAL. The substance labelling `kind` is DATA
  carried by the decomposition, not derived from the 8-tuple (`FlowEdge` has no
  substance slot — see `Decomposition.lean`'s design note). So `rekind_refused`
  is stated against the model TOGETHER WITH its declared labelling: it refuses
  `childWith 9` under the toy's own substance tags. A modeller free to relabel
  after the fact could always declare two different substances equal; that is a
  statement about labelling discipline upstream, not about this contract. -/

namespace FedInterfaceSplit

/-! ### The parent: one interface carrying two membrane crossings -/

/-- The Balance Sheet — the parent's interface component, the one being split. -/
def balanceSheet : ℕ := 10
/-- The Open Market Desk — an interior component feeding the Balance Sheet. -/
def openMarketDesk : ℕ := 11
/-- The Treasury — an environmental object that sends across the membrane. -/
def treasury : ℕ := 20
/-- The Banks — an environmental object that receives across the membrane. -/
def banks : ℕ := 21
/-- The TGA account — a child mechanism, receiver side. -/
def tgaAccount : ℕ := 30
/-- The reserve accounts — a child mechanism, exporter side. -/
def reserveAccounts : ℕ := 31

/-- The toy uses the capacity slot as the substance tag, because `FlowEdge` has
    no substance field and `Decomposition`/`InterfaceDecomposition` therefore
    take the labelling as external data. `1` = message, `2` = deposit,
    `3` = reserves. -/
def substanceTag : FlowEdge ℕ ℕ → ℕ := fun e => e.capacity

/-- Interior flow: the Desk instructs the Balance Sheet (message). -/
def pIn : FlowEdge ℕ ℕ := ⟨openMarketDesk, balanceSheet, 1⟩
/-- Membrane crossing IN: the Treasury deposits (deposit). -/
def pExoIn : FlowEdge ℕ ℕ := ⟨treasury, balanceSheet, 2⟩
/-- Membrane crossing OUT: the Balance Sheet credits the Banks (reserves). -/
def pExoOut : FlowEdge ℕ ℕ := ⟨balanceSheet, banks, 3⟩

/-- N: the parent's internal network — one edge, Desk → Balance Sheet. -/
def parentN : FlowNetwork ℕ ℕ where
  nodes := {balanceSheet, openMarketDesk}
  edges := {pIn}
  edges_on := by
    intro e he
    have he' : e = pIn := he
    subst he'
    exact ⟨Or.inr rfl, Or.inl rfl⟩
  no_self_loops := by
    intro e he
    have he' : e = pIn := he
    subst he'
    exact Nat.succ_ne_self 10

/-- G: the parent's external flows — the two membrane crossings. -/
def parentG : FlowNetwork ℕ ℕ where
  nodes := {balanceSheet, treasury, banks}
  edges := {pExoIn, pExoOut}
  edges_on := by
    intro e he
    have he' : e = pExoIn ∨ e = pExoOut := he
    rcases he' with rfl | rfl
    · exact ⟨Or.inr (Or.inl rfl), Or.inl rfl⟩
    · exact ⟨Or.inl rfl, Or.inr (Or.inr rfl)⟩
  no_self_loops := by
    intro e he
    have he' : e = pExoIn ∨ e = pExoOut := he
    rcases he' with rfl | rfl <;> decide

/-- The parent 8-tuple. `μ, π, τ, η, δ := Unit` — none of them enters a
    coherence constraint or the decomposition contract. -/
def fedParent : MobusSystem ℕ ℕ Unit Unit Unit Unit Unit where
  components := {balanceSheet, openMarketDesk}
  internalNetwork := parentN
  environment := ⟨{treasury, banks}, ()⟩
  externalFlows := parentG
  boundary := ⟨(), {balanceSheet}⟩
  transforms := ()
  history := ()
  timeScale := ()
  network_components := rfl
  disjoint := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro (rfl | rfl) <;> decide
  interfaces_sub := by
    intro n hn
    have hn' : n = balanceSheet := hn
    exact Or.inl hn'
  bipartite := by
    intro e he
    have he' : e = pExoIn ∨ e = pExoOut := he
    rcases he' with rfl | rfl
    · exact Or.inl ⟨Or.inl rfl, rfl⟩
    · exact Or.inr ⟨rfl, Or.inr rfl⟩
  externalFlows_nodes := by
    intro n hn
    have hn' : n = balanceSheet ∨ n = treasury ∨ n = banks := hn
    rcases hn' with rfl | rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr rfl)
  interfaces_carry_flow := by
    intro i hi
    have hi' : i = balanceSheet := hi
    subst hi'
    exact ⟨pExoIn, Or.inl rfl, Or.inr rfl⟩

/-! ### What the parent's flows at the Balance Sheet are -/

theorem inflows_eq : inflows fedParent balanceSheet = {pIn} := by
  ext e
  constructor
  · rintro ⟨he, _⟩
    exact he
  · rintro rfl
    exact ⟨rfl, rfl⟩

theorem outflows_eq : outflows fedParent balanceSheet = ∅ := by
  ext e
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨he, hs⟩
  have he' : e = pIn := he
  subst he'
  exact absurd hs (by decide)

theorem exoInflows_eq : exoInflows fedParent balanceSheet = {pExoIn} := by
  ext e
  constructor
  · rintro ⟨he, ht⟩
    have he' : e = pExoIn ∨ e = pExoOut := he
    rcases he' with rfl | rfl
    · rfl
    · exact absurd ht (by decide)
  · rintro rfl
    exact ⟨Or.inl rfl, rfl⟩

theorem exoOutflows_eq : exoOutflows fedParent balanceSheet = {pExoOut} := by
  ext e
  constructor
  · rintro ⟨he, hs⟩
    have he' : e = pExoIn ∨ e = pExoOut := he
    rcases he' with rfl | rfl
    · exact absurd hs (by decide)
    · rfl
  · rintro rfl
    exact ⟨Or.inr rfl, rfl⟩

/-! ### The child family — the Balance Sheet split into two mechanisms

  Parameterized by the substance tag `k` on the Treasury crossing so the passing
  model (`k = 2`, tag preserved) and the re-kinding model (`k = 9`) share every
  8-tuple coherence proof: they differ only in a slot no constraint touches. -/

/-- Interior boundary flow: the Desk's stand-in instructs the TGA account. -/
def cIn : FlowEdge ℕ ℕ := ⟨openMarketDesk, tgaAccount, 1⟩
/-- The Treasury crossing, refined: it now lands on the TGA account. -/
def cExoIn (k : ℕ) : FlowEdge ℕ ℕ := ⟨treasury, tgaAccount, k⟩
/-- The Banks crossing, refined: it now leaves from the reserve accounts. -/
def cExoOut : FlowEdge ℕ ℕ := ⟨reserveAccounts, banks, 3⟩

/-- N′: the child's internal network. The two mechanisms do not interact
    directly in this toy; interior structure plays no part in the seam. -/
def childN : FlowNetwork ℕ ℕ where
  nodes := {tgaAccount, reserveAccounts}
  edges := ∅
  edges_on := by intro e he; exact absurd he (Set.notMem_empty e)
  no_self_loops := by intro e he; exact absurd he (Set.notMem_empty e)

/-- G′: the child's boundary flows — one interior coupling and the two refined
    membrane crossings. -/
def childG (k : ℕ) : FlowNetwork ℕ ℕ where
  nodes := {openMarketDesk, treasury, banks, tgaAccount, reserveAccounts}
  edges := {cIn, cExoIn k, cExoOut}
  edges_on := by
    intro e he
    have he' : e = cIn ∨ e = cExoIn k ∨ e = cExoOut := he
    rcases he' with rfl | rfl | rfl
    · exact ⟨Or.inl rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr rfl))), Or.inr (Or.inr (Or.inl rfl))⟩
  no_self_loops := by
    intro e he
    have he' : e = cIn ∨ e = cExoIn k ∨ e = cExoOut := he
    rcases he' with rfl | rfl | rfl
    · exact (by decide : openMarketDesk ≠ tgaAccount)
    · exact (by decide : treasury ≠ tgaAccount)
    · exact (by decide : reserveAccounts ≠ banks)

/-- The child 8-tuple. `E′` holds the Desk's stand-in AND the two environmental
    objects the parent couples to through the Balance Sheet — the widening
    `InterfaceDecomposition.derived_env` demands. -/
def childWith (k : ℕ) : MobusSystem ℕ ℕ Unit Unit Unit Unit Unit where
  components := {tgaAccount, reserveAccounts}
  internalNetwork := childN
  environment := ⟨{openMarketDesk, treasury, banks}, ()⟩
  externalFlows := childG k
  boundary := ⟨(), {tgaAccount, reserveAccounts}⟩
  transforms := ()
  history := ()
  timeScale := ()
  network_components := rfl
  disjoint := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro (rfl | rfl) <;> decide
  interfaces_sub := fun _ h => h
  bipartite := by
    intro e he
    have he' : e = cIn ∨ e = cExoIn k ∨ e = cExoOut := he
    rcases he' with rfl | rfl | rfl
    · exact Or.inl ⟨Or.inl rfl, Or.inl rfl⟩
    · exact Or.inl ⟨Or.inr (Or.inl rfl), Or.inl rfl⟩
    · exact Or.inr ⟨Or.inr rfl, Or.inr (Or.inr rfl)⟩
  externalFlows_nodes := by
    intro n hn
    have hn' : n = openMarketDesk ∨ n = treasury ∨ n = banks ∨
        n = tgaAccount ∨ n = reserveAccounts := hn
    rcases hn' with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr (Or.inl rfl))
    · exact Or.inl (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  interfaces_carry_flow := by
    intro i hi
    have hi' : i = tgaAccount ∨ i = reserveAccounts := hi
    rcases hi' with rfl | rfl
    · exact ⟨cIn, Or.inl rfl, Or.inr rfl⟩
    · exact ⟨cExoOut, Or.inr (Or.inr rfl), Or.inl rfl⟩

/-! ### The child's boundary flows, computed -/

/-- `O` throughout: the parent's environmental objects. -/
theorem parent_env : fedParent.environment.objects = {treasury, banks} := rfl

theorem childSources_eq (k : ℕ) :
    childSources (childWith k) = {cIn, cExoIn k} := by
  ext e
  constructor
  · rintro ⟨he, hs⟩
    have he' : e = cIn ∨ e = cExoIn k ∨ e = cExoOut := he
    rcases he' with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have hs' : cExoOut.source = openMarketDesk ∨ cExoOut.source = treasury ∨
          cExoOut.source = banks := hs
      rcases hs' with h | h | h <;> exact absurd h (by decide)
  · intro he
    have he' : e = cIn ∨ e = cExoIn k := he
    rcases he' with rfl | rfl
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inl rfl)⟩

theorem childSinks_eq (k : ℕ) : childSinks (childWith k) = {cExoOut} := by
  ext e
  constructor
  · rintro ⟨he, ht⟩
    have he' : e = cIn ∨ e = cExoIn k ∨ e = cExoOut := he
    rcases he' with rfl | rfl | rfl
    · have ht' : cIn.target = openMarketDesk ∨ cIn.target = treasury ∨
        cIn.target = banks := ht
      rcases ht' with h | h | h <;> exact absurd h (by decide)
    · have ht' : tgaAccount = openMarketDesk ∨ tgaAccount = treasury ∨
        tgaAccount = banks := ht
      rcases ht' with h | h | h <;> exact absurd h (by decide)
    · rfl
  · intro he
    have he' : e = cExoOut := he
    subst he'
    exact ⟨Or.inr (Or.inr rfl), Or.inr (Or.inr rfl)⟩

theorem interiorSources_eq (k : ℕ) :
    interiorSources (childWith k) fedParent.environment.objects = {cIn} := by
  ext e
  constructor
  · rintro ⟨he, hs⟩
    rw [childSources_eq k] at he
    have he' : e = cIn ∨ e = cExoIn k := he
    rcases he' with rfl | rfl
    · rfl
    · exact absurd (Or.inl rfl : (cExoIn k).source = treasury ∨
        (cExoIn k).source = banks) hs
  · intro he
    have he' : e = cIn := he
    subst he'
    refine ⟨by rw [childSources_eq]; exact Or.inl rfl, ?_⟩
    intro h
    have h' : cIn.source = treasury ∨ cIn.source = banks := h
    rcases h' with h | h <;> exact absurd h (by decide)

theorem crossingSources_eq (k : ℕ) :
    crossingSources (childWith k) fedParent.environment.objects = {cExoIn k} := by
  ext e
  constructor
  · rintro ⟨he, hs⟩
    rw [childSources_eq k] at he
    have he' : e = cIn ∨ e = cExoIn k := he
    rcases he' with rfl | rfl
    · have hs' : cIn.source = treasury ∨ cIn.source = banks := hs
      rcases hs' with h | h <;> exact absurd h (by decide)
    · rfl
  · intro he
    have he' : e = cExoIn k := he
    subst he'
    exact ⟨by rw [childSources_eq]; exact Or.inr rfl, Or.inl rfl⟩

theorem interiorSinks_eq (k : ℕ) :
    interiorSinks (childWith k) fedParent.environment.objects = ∅ := by
  ext e
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨he, ht⟩
  rw [childSinks_eq k] at he
  have he' : e = cExoOut := he
  subst he'
  exact ht (Or.inr rfl)

theorem crossingSinks_eq (k : ℕ) :
    crossingSinks (childWith k) fedParent.environment.objects = {cExoOut} := by
  ext e
  constructor
  · rintro ⟨he, _⟩
    rw [childSinks_eq k] at he
    exact he
  · intro he
    have he' : e = cExoOut := he
    subst he'
    exact ⟨by rw [childSinks_eq]; rfl, Or.inr rfl⟩

/-! ### `E′` is exactly the derived neighbourhood

  The interior neighbourhood of the Balance Sheet is the Desk; its EXTERNAL
  neighbourhood is the Treasury and the Banks. `Decomposition.derived_env` would
  demand only the first, which is precisely why it cannot describe this child. -/

theorem derived_env_eq (k : ℕ) :
    (childWith k).environment.objects =
      (fedParent.internalNetwork.successors balanceSheet ∪
        fedParent.internalNetwork.predecessors balanceSheet) ∪
      (fedParent.externalFlows.successors balanceSheet ∪
        fedParent.externalFlows.predecessors balanceSheet) := by
  ext n
  constructor
  · intro hn
    have hn' : n = openMarketDesk ∨ n = treasury ∨ n = banks := hn
    rcases hn' with rfl | rfl | rfl
    · exact Or.inl (Or.inr ⟨pIn, rfl, rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨pExoIn, Or.inl rfl, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨pExoOut, Or.inr rfl, rfl, rfl⟩)
  · rintro ((⟨e, he, hs, ht⟩ | ⟨e, he, hs, ht⟩) | (⟨e, he, hs, ht⟩ | ⟨e, he, hs, ht⟩))
    · have he' : e = pIn := he
      subst he'
      exact absurd hs (by decide)
    · have he' : e = pIn := he
      subst he'
      exact Or.inl hs.symm
    · have he' : e = pExoIn ∨ e = pExoOut := he
      rcases he' with rfl | rfl
      · exact absurd hs (by decide)
      · exact Or.inr (Or.inr ht.symm)
    · have he' : e = pExoIn ∨ e = pExoOut := he
      rcases he' with rfl | rfl
      · exact Or.inr (Or.inl hs.symm)
      · exact absurd ht (by decide)

/-! ### The four contract bijections -/

/-- Any two singletons of the same type are equivalent. The seam equivalences
    below are all singleton-to-singleton or empty-to-empty; this is the bridge
    that turns the computed set equalities into `Equiv`s. -/
private def singletonEquiv {X : Type*} (a b : X) : ({a} : Set X) ≃ ({b} : Set X) where
  toFun _ := ⟨b, rfl⟩
  invFun _ := ⟨a, rfl⟩
  left_inv := fun x => Subtype.ext x.2.symm
  right_inv := fun y => Subtype.ext y.2.symm

/-- Interior source half: the Desk's boundary flow ↔ the parent's interior
    inflow at the Balance Sheet. -/
def βsrcFed (k : ℕ) :
    interiorSources (childWith k) fedParent.environment.objects ≃
      inflows fedParent balanceSheet :=
  (Equiv.setCongr (interiorSources_eq k)).trans
    ((singletonEquiv cIn pIn).trans (Equiv.setCongr inflows_eq).symm)

/-- Interior sink half: both sides empty — the Balance Sheet has no interior
    outflow in this toy. -/
def βsnkFed (k : ℕ) :
    interiorSinks (childWith k) fedParent.environment.objects ≃
      outflows fedParent balanceSheet :=
  Equiv.setCongr ((interiorSinks_eq k).trans outflows_eq.symm)

/-- CROSSING, receiver half: the Treasury→TGA flow ↔ the parent's Treasury
    crossing into the Balance Sheet. -/
def γsrcFed (k : ℕ) :
    crossingSources (childWith k) fedParent.environment.objects ≃
      exoInflows fedParent balanceSheet :=
  (Equiv.setCongr (crossingSources_eq k)).trans
    ((singletonEquiv (cExoIn k) pExoIn).trans (Equiv.setCongr exoInflows_eq).symm)

/-- CROSSING, exporter half: the reserve-accounts→Banks flow ↔ the parent's
    crossing out of the Balance Sheet. -/
def γsnkFed (k : ℕ) :
    crossingSinks (childWith k) fedParent.environment.objects ≃
      exoOutflows fedParent balanceSheet :=
  (Equiv.setCongr (crossingSinks_eq k)).trans
    ((singletonEquiv cExoOut pExoOut).trans (Equiv.setCongr exoOutflows_eq).symm)

/-! ### The passing instance -/

/-- **The toy 2-protocol interface split satisfies the contract.**

    The Balance Sheet — a parent INTERFACE, which `Decomposition` cannot touch —
    decomposes into a TGA account and reserve accounts. Both membrane crossings
    survive with their counterparty (`xsrc_env_preserved`, `xsnk_env_preserved`),
    their substance tag, and a named child interface member to land on; the
    interior flow from the Desk keeps the ordinary `βsrc` treatment. -/
def fedSplit : InterfaceDecomposition ℕ ℕ Unit Unit Unit Unit Unit ℕ where
  parent := fedParent
  comp := balanceSheet
  child := childWith 2
  kind := substanceTag
  comp_mem := Or.inl rfl
  comp_interface := rfl
  βsrc := βsrcFed 2
  βsnk := βsnkFed 2
  γsrc := γsrcFed 2
  γsnk := γsnkFed 2
  src_preserves_kind := by
    intro e
    have hv : (↑e : FlowEdge ℕ ℕ) = cIn := by
      have h : (↑e : FlowEdge ℕ ℕ) ∈ ({cIn} : Set (FlowEdge ℕ ℕ)) := by
        rw [← interiorSources_eq 2]; exact e.2
      exact h
    show substanceTag pIn = substanceTag (↑e)
    rw [hv]; rfl
  snk_preserves_kind := by
    intro e
    have h : (↑e : FlowEdge ℕ ℕ) ∈ (∅ : Set (FlowEdge ℕ ℕ)) := by
      rw [← interiorSinks_eq 2]; exact e.2
    exact absurd h (Set.notMem_empty _)
  xsrc_preserves_kind := by
    intro e
    have hv : (↑e : FlowEdge ℕ ℕ) = cExoIn 2 := by
      have h : (↑e : FlowEdge ℕ ℕ) ∈ ({cExoIn 2} : Set (FlowEdge ℕ ℕ)) := by
        rw [← crossingSources_eq 2]; exact e.2
      exact h
    show substanceTag pExoIn = substanceTag (↑e)
    rw [hv]; rfl
  xsnk_preserves_kind := by
    intro e
    have hv : (↑e : FlowEdge ℕ ℕ) = cExoOut := by
      have h : (↑e : FlowEdge ℕ ℕ) ∈ ({cExoOut} : Set (FlowEdge ℕ ℕ)) := by
        rw [← crossingSinks_eq 2]; exact e.2
      exact h
    show substanceTag pExoOut = substanceTag (↑e)
    rw [hv]; rfl
  xsrc_env_preserved := by
    intro e
    have hv : (↑e : FlowEdge ℕ ℕ) = cExoIn 2 := by
      have h : (↑e : FlowEdge ℕ ℕ) ∈ ({cExoIn 2} : Set (FlowEdge ℕ ℕ)) := by
        rw [← crossingSources_eq 2]; exact e.2
      exact h
    show pExoIn.source = (↑e : FlowEdge ℕ ℕ).source
    rw [hv]; rfl
  xsnk_env_preserved := by
    intro e
    have hv : (↑e : FlowEdge ℕ ℕ) = cExoOut := by
      have h : (↑e : FlowEdge ℕ ℕ) ∈ ({cExoOut} : Set (FlowEdge ℕ ℕ)) := by
        rw [← crossingSinks_eq 2]; exact e.2
      exact h
    show pExoOut.target = (↑e : FlowEdge ℕ ℕ).target
    rw [hv]; rfl
  src_lands := by
    intro e he
    rw [childSources_eq 2] at he
    have he' : e = cIn ∨ e = cExoIn 2 := he
    rcases he' with rfl | rfl <;> exact Or.inl rfl
  snk_lands := by
    intro e he
    rw [childSinks_eq 2] at he
    have he' : e = cExoOut := he
    subst he'
    exact Or.inr rfl
  derived_env := derived_env_eq 2

/-- The contract is SATISFIABLE on a boundary component: a decomposition of a
    parent interface exists. Without this, the refusals below would be the
    vacuous kind of separation. -/
theorem interface_decomposition_inhabited :
    ∃ d : InterfaceDecomposition ℕ ℕ Unit Unit Unit Unit Unit ℕ,
      d.comp ∈ d.parent.boundary.interfaces :=
  ⟨fedSplit, fedSplit.comp_interface⟩

/-! ### Separating instance 1 — a dropped membrane crossing -/

/-- G′ with the Treasury crossing removed: the TGA account no longer receives
    from the Treasury, though `E′` still declares the Treasury. -/
def droppedG : FlowNetwork ℕ ℕ where
  nodes := {openMarketDesk, banks, tgaAccount, reserveAccounts}
  edges := {cIn, cExoOut}
  edges_on := by
    intro e he
    have he' : e = cIn ∨ e = cExoOut := he
    rcases he' with rfl | rfl
    · exact ⟨Or.inl rfl, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨Or.inr (Or.inr (Or.inr rfl)), Or.inr (Or.inl rfl)⟩
  no_self_loops := by
    intro e he
    have he' : e = cIn ∨ e = cExoOut := he
    rcases he' with rfl | rfl <;> decide

/-- The child that ABSORBS the Treasury crossing instead of refining it. Every
    8-tuple coherence constraint still holds, and `derived_env` still holds —
    the model is well formed. It fails only the crossing contract. -/
def droppedChild : MobusSystem ℕ ℕ Unit Unit Unit Unit Unit where
  components := {tgaAccount, reserveAccounts}
  internalNetwork := childN
  environment := ⟨{openMarketDesk, treasury, banks}, ()⟩
  externalFlows := droppedG
  boundary := ⟨(), {tgaAccount, reserveAccounts}⟩
  transforms := ()
  history := ()
  timeScale := ()
  network_components := rfl
  disjoint := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro (rfl | rfl) <;> decide
  interfaces_sub := fun _ h => h
  bipartite := by
    intro e he
    have he' : e = cIn ∨ e = cExoOut := he
    rcases he' with rfl | rfl
    · exact Or.inl ⟨Or.inl rfl, Or.inl rfl⟩
    · exact Or.inr ⟨Or.inr rfl, Or.inr (Or.inr rfl)⟩
  externalFlows_nodes := by
    intro n hn
    have hn' : n = openMarketDesk ∨ n = banks ∨ n = tgaAccount ∨
        n = reserveAccounts := hn
    rcases hn' with rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  interfaces_carry_flow := by
    intro i hi
    have hi' : i = tgaAccount ∨ i = reserveAccounts := hi
    rcases hi' with rfl | rfl
    · exact ⟨cIn, Or.inl rfl, Or.inr rfl⟩
    · exact ⟨cExoOut, Or.inr rfl, Or.inl rfl⟩

/-- `droppedChild` satisfies `derived_env` — its `E′` is exactly the derived
    neighbourhood, Treasury included. The refusal below is therefore NOT the
    environment condition firing: the child still declares the counterparty it
    has stopped receiving from. -/
theorem droppedChild_derived_env :
    droppedChild.environment.objects =
      (fedParent.internalNetwork.successors balanceSheet ∪
        fedParent.internalNetwork.predecessors balanceSheet) ∪
      (fedParent.externalFlows.successors balanceSheet ∪
        fedParent.externalFlows.predecessors balanceSheet) :=
  derived_env_eq 2

/-- No child boundary flow crosses in from a parent environmental object. -/
theorem droppedChild_no_crossingSources :
    crossingSources droppedChild fedParent.environment.objects = ∅ := by
  ext e
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨he, _⟩, hs⟩
  have he' : e = cIn ∨ e = cExoOut := he
  rcases he' with rfl | rfl
  · have hs' : cIn.source = treasury ∨ cIn.source = banks := hs
    rcases hs' with h | h <;> exact absurd h (by decide)
  · have hs' : cExoOut.source = treasury ∨ cExoOut.source = banks := hs
    rcases hs' with h | h <;> exact absurd h (by decide)

/-- **SEPARATION 1: dropping a membrane crossing is refused.** No
    `InterfaceDecomposition` of the Balance Sheet into `droppedChild` exists.
    The parent still sends the Treasury flow across its membrane at the Balance
    Sheet, and `γsrc` has nothing on the child side to carry it — so the seam
    that `exoInflow_continues` promises cannot be built. This is the check
    biting: the model is a well-formed 8-tuple and passes every constraint the
    kernel had before this file. -/
theorem crossing_dropped_refused
    (d : InterfaceDecomposition ℕ ℕ Unit Unit Unit Unit Unit ℕ)
    (hp : d.parent = fedParent) (hc : d.comp = balanceSheet)
    (hch : d.child = droppedChild) : False := by
  have hmem : pExoIn ∈ exoInflows d.parent d.comp := by
    rw [hp, hc, exoInflows_eq]; rfl
  obtain ⟨e, -, -⟩ := d.exoInflow_continues ⟨pExoIn, hmem⟩
  have h : (↑e : FlowEdge ℕ ℕ) ∈
      crossingSources droppedChild fedParent.environment.objects := by
    rw [← hch, ← hp]; exact e.2
  rw [droppedChild_no_crossingSources] at h
  exact absurd h (Set.notMem_empty _)

/-! ### Separating instance 2 — a re-kinded membrane crossing -/

/-- **SEPARATION 2: re-kinding a membrane crossing is refused.** `childWith 9`
    keeps the Treasury crossing and lands it on a named interface member, so it
    passes every bijection and every landing condition — but it declares the
    inbound substance as tag `9` where the parent declared `2`. The contract
    refuses it. Stated against the model TOGETHER WITH its declared labelling
    (`hk`), because the substance labelling is data the decomposition carries,
    not a fact derivable from the 8-tuple. -/
theorem rekind_refused
    (d : InterfaceDecomposition ℕ ℕ Unit Unit Unit Unit Unit ℕ)
    (hp : d.parent = fedParent) (hc : d.comp = balanceSheet)
    (hch : d.child = childWith 9) (hk : d.kind = substanceTag) : False := by
  have hmem : pExoIn ∈ exoInflows d.parent d.comp := by
    rw [hp, hc, exoInflows_eq]; rfl
  obtain ⟨e, ⟨-, -, hkind, -⟩, -⟩ := d.crossing_refines_inflow ⟨pExoIn, hmem⟩
  have hv' : (↑e : FlowEdge ℕ ℕ) = cExoIn 9 := by
    have hv : (↑e : FlowEdge ℕ ℕ) ∈ ({cExoIn 9} : Set (FlowEdge ℕ ℕ)) := by
      rw [← crossingSources_eq 9, ← hch, ← hp]; exact e.2
    exact hv
  rw [hk, hv'] at hkind
  -- the parent declared substance tag `2` on the Treasury crossing, the child `9`
  have htag : (9 : ℕ) = 2 := hkind
  exact absurd htag (by decide)

/-- **The crossing contract separates.** It is satisfiable on a boundary
    component (`fedSplit`), and it refuses both a child that drops a membrane
    crossing and a child that re-kinds one. Neither refusal comes from a
    malformed 8-tuple: `droppedChild` and `childWith 9` are both valid
    `MobusSystem`s satisfying every coherence constraint the kernel carried
    before SSF #43, and both satisfy `derived_env`. -/
theorem crossing_contract_separates :
    (∃ d : InterfaceDecomposition ℕ ℕ Unit Unit Unit Unit Unit ℕ,
        d.comp ∈ d.parent.boundary.interfaces) ∧
    (∀ d : InterfaceDecomposition ℕ ℕ Unit Unit Unit Unit Unit ℕ,
        d.parent = fedParent → d.comp = balanceSheet → d.child = droppedChild → False) ∧
    (∀ d : InterfaceDecomposition ℕ ℕ Unit Unit Unit Unit Unit ℕ,
        d.parent = fedParent → d.comp = balanceSheet → d.child = childWith 9 →
        d.kind = substanceTag → False) :=
  ⟨interface_decomposition_inhabited, crossing_dropped_refused, rekind_refused⟩

end FedInterfaceSplit

end Systems
