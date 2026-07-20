/-
  Systems/Core/Decomposition.lean
  Hierarchical decomposition by reference — the seam contract (bert-lenses#89)

  Formalizes the three statements that gate bert-lenses#89, stated over the
  Lean-specified 8-tuple S = ⟨C, N, E, G, B, T, H, Δt⟩ (Tuple.lean, the
  semantic authority), per §5 of
  `bert-lenses/docs/design/decomposition-foundations.md`:

  1. **The seam structure** (`Decomposition`): a parent 8-tuple, a chosen
     component `c`, a child 8-tuple, and the boundary contract — a pair of
     equivalences `βsrc`, `βsnk` witnessing `β : Src′ ⊎ Snk′ ≅ in(c) ⊎ out(c)`
     with (i) direction-preservation (by construction — inflows biject with
     child sources, outflows with child sinks), (ii) substance-kind
     preservation, (iii) interface-landing. The child's environment `E′` is a
     DERIVED field: the parent's interior neighborhood of `c`. This last
     condition is what `RecursiveSystem` lacks and what the 8-tuple's
     first-class `E` makes statable (the printed 7-tuple folds E into G and
     cannot express it — see decomposition-foundations.md §5.1).

  2. **Assembly** (`assembleDepth1`, `assembleDepth1_wellFormed`): a parent
     with a covering list of well-formed child `RecursiveSystem`s assembles
     into a `WellFormed` `RecursiveSystem`. This is the "by-reference and
     in-place are the same mathematics" theorem — the assembled composite is
     well-formed whether the decomposed slot is an unexpanded reference stub
     (a primitive) or a fully expanded child subtree (`decompose_one_wellFormed`).
     PROVEN AT DEPTH 1; arbitrary-depth Mobus→Bunge assembly driven by each
     edge's β is a documented conjecture below, not formalized here.

  3. **Substitution soundness** (`substitution_sound`, `seam_*`): substituting
     a contracted child for its component preserves the structural seam — the
     `seam` equivalence is a bijection between the parent's flows at `c` and
     the child's boundary flows that preserves both substance kind and
     direction (`seam_bijective`, `seam_preserves_kind`, `seam_inl`/`seam_inr`),
     so every parent flow at `c` continues into exactly one child flow
     (`inflow_continues`, `outflow_continues`). Structural only: NO claim about
     T composition or Δt (the deferred dynamical face). Verdict-preservation
     across levels is likewise NOT proven — conjectured below.

  DESIGN — substance kind. The codebase's `FlowEdge` carries only
  ⟨source, target, capacity⟩; it has no substance-kind slot (matter / energy /
  message). Property (ii) therefore introduces substance kind as an explicit
  labeling `kind : FlowEdge α κ → σ` carried by the `Decomposition`. This is
  the one place the contract's math needs a kernel notion that does not yet
  exist in the Lean 8-tuple — flagged for the kernel step (foundations doc §7.2).
-/

import Systems.Mobus.Bridge
import Systems.Core.Systemness
import Mathlib.Logic.Equiv.Basic

namespace Systems

variable {α : Type*} {κ μ π τ η δ σ : Type*}

/-! ## Parent-incident and child-boundary flow sets

  `flows(c) ⊆ N` split as `in(c) ⊎ out(c)` (parent internal edges incident to
  `c`), and the child's boundary flows `Src′ ⊎ Snk′` read off `G′` by
  direction. These four sets are the carriers of the seam bijection. -/

/-- `in(c)`: parent internal-network edges flowing INTO the chosen component. -/
def inflows (S : MobusSystem α κ μ π τ η δ) (c : α) : Set (FlowEdge α κ) :=
  {e | e ∈ S.internalNetwork.edges ∧ e.target = c}

/-- `out(c)`: parent internal-network edges flowing OUT of the chosen component. -/
def outflows (S : MobusSystem α κ μ π τ η δ) (c : α) : Set (FlowEdge α κ) :=
  {e | e ∈ S.internalNetwork.edges ∧ e.source = c}

/-- `Src′`: child external-flow edges inbound from the child's environment
    (source ∈ O′). By the child's `bipartite` constraint the target of such an
    edge is an interface component — the child-side terminal the contract lands on. -/
def childSources (S : MobusSystem α κ μ π τ η δ) : Set (FlowEdge α κ) :=
  {e | e ∈ S.externalFlows.edges ∧ e.source ∈ S.environment.objects}

/-- `Snk′`: child external-flow edges outbound to the child's environment
    (target ∈ O′). The source of such an edge is an interface component. -/
def childSinks (S : MobusSystem α κ μ π τ η δ) : Set (FlowEdge α κ) :=
  {e | e ∈ S.externalFlows.edges ∧ e.target ∈ S.environment.objects}

/-! ## Statement 1 — the seam structure -/

/-- A decomposition of component `comp` of `parent` into `child`, by reference.

    The boundary contract `β : Src′ ⊎ Snk′ ≅ in(c) ⊎ out(c)` is carried as two
    equivalences so that **direction-preservation holds by construction**:
    `βsrc` bijects the child's sources with `c`'s inflows, `βsnk` the child's
    sinks with `c`'s outflows. Substance-kind preservation and interface-landing
    are the remaining `Prop` fields; the child's environment `E′` is derived
    from the parent's interior neighborhood of `comp` (`derived_env`) — the
    condition `RecursiveSystem` cannot state.

    Parametric slots `T′, H′, Δt′` do not appear: they are level-local
    (`H` = History, not hierarchy) or belong to the deferred dynamical face. -/
structure Decomposition (α κ μ π τ η δ σ : Type*) where
  /-- The parent flat 8-tuple (one level). -/
  parent : MobusSystem α κ μ π τ η δ
  /-- The complex component being decomposed. -/
  comp : α
  /-- The child flat 8-tuple that replaces `comp`'s opacity. -/
  child : MobusSystem α κ μ π τ η δ
  /-- Substance-kind label on flow edges (matter / energy / message).
      Introduced here because `FlowEdge` carries no substance slot. -/
  kind : FlowEdge α κ → σ
  /-- The decomposed component is a genuine parent component. -/
  comp_mem : comp ∈ parent.components
  /-- Contract, source half: child sources biject with `c`'s inflows. -/
  βsrc : childSources child ≃ inflows parent comp
  /-- Contract, sink half: child sinks biject with `c`'s outflows. -/
  βsnk : childSinks child ≃ outflows parent comp
  /-- (ii) `βsrc` preserves substance kind. -/
  src_preserves_kind :
    ∀ e : childSources child, kind (↑(βsrc e) : FlowEdge α κ) = kind (↑e : FlowEdge α κ)
  /-- (ii) `βsnk` preserves substance kind. -/
  snk_preserves_kind :
    ∀ e : childSinks child, kind (↑(βsnk e) : FlowEdge α κ) = kind (↑e : FlowEdge α κ)
  /-- (iii) each child source lands on a child interface component (its target). -/
  src_lands : ∀ e ∈ childSources child, e.target ∈ child.boundary.interfaces
  /-- (iii) each child sink lands on a child interface component (its source). -/
  snk_lands : ∀ e ∈ childSinks child, e.source ∈ child.boundary.interfaces
  /-- `E′` is DERIVED: the parent's interior neighborhood of `comp`
      (its predecessors and successors in `N`). Nothing else may appear in `E′`. -/
  derived_env : child.environment.objects =
    parent.internalNetwork.successors comp ∪ parent.internalNetwork.predecessors comp

namespace Decomposition

/-! ## Statement 3 — substitution soundness (structural)

  The seam is a kind- and direction-preserving bijection between the parent's
  flows at `comp` and the child's boundary flows. Substituting the child for
  `comp` conserves flow: every parent flow at the seam continues into exactly
  one child flow through β. No `T`/`Δt` content. -/

/-- The seam bijection `β : Src′ ⊎ Snk′ ≅ in(c) ⊎ out(c)`, assembled from the
    two direction-typed halves. -/
def seam (d : Decomposition α κ μ π τ η δ σ) :
    (childSources d.child ⊕ childSinks d.child) ≃
      (inflows d.parent d.comp ⊕ outflows d.parent d.comp) :=
  Equiv.sumCongr d.βsrc d.βsnk

/-- Direction-preservation, source half: sources map to inflows (`inl ↦ inl`). -/
@[simp] theorem seam_inl (d : Decomposition α κ μ π τ η δ σ)
    (e : childSources d.child) : d.seam (Sum.inl e) = Sum.inl (d.βsrc e) := rfl

/-- Direction-preservation, sink half: sinks map to outflows (`inr ↦ inr`). -/
@[simp] theorem seam_inr (d : Decomposition α κ μ π τ η δ σ)
    (e : childSinks d.child) : d.seam (Sum.inr e) = Sum.inr (d.βsnk e) := rfl

/-- Flow conservation: the seam is a bijection (each parent flow at `comp`
    corresponds to exactly one child boundary flow, and conversely). -/
theorem seam_bijective (d : Decomposition α κ μ π τ η δ σ) :
    Function.Bijective d.seam :=
  d.seam.bijective

/-- Each parent inflow at `comp` continues into exactly one child source. -/
theorem inflow_continues (d : Decomposition α κ μ π τ η δ σ)
    (p : inflows d.parent d.comp) : ∃! e : childSources d.child, d.βsrc e = p :=
  d.βsrc.bijective.existsUnique p

/-- Each parent outflow at `comp` continues into exactly one child sink. -/
theorem outflow_continues (d : Decomposition α κ μ π τ η δ σ)
    (p : outflows d.parent d.comp) : ∃! e : childSinks d.child, d.βsnk e = p :=
  d.βsnk.bijective.existsUnique p

/-- The underlying flow edge of a boundary-flow element, on either side. -/
private def edgeOf {A B : Set (FlowEdge α κ)} : A ⊕ B → FlowEdge α κ :=
  Sum.elim (fun e => ↑e) (fun e => ↑e)

/-- Substance-kind preservation across the whole seam. -/
theorem seam_preserves_kind (d : Decomposition α κ μ π τ η δ σ)
    (x : childSources d.child ⊕ childSinks d.child) :
    d.kind (edgeOf (d.seam x)) = d.kind (edgeOf x) := by
  cases x with
  | inl e => simp only [seam_inl, edgeOf, Sum.elim_inl]; exact d.src_preserves_kind e
  | inr e => simp only [seam_inr, edgeOf, Sum.elim_inr]; exact d.snk_preserves_kind e

/-- **Statement 3 (Eq. 4.3, structural).** Substituting the contracted child
    for `comp` preserves the seam: `seam` is a bijection that preserves flow
    direction (`inl`/`inr`) and substance kind. Purely structural — no `T`
    composition, no `Δt`. -/
theorem substitution_sound (d : Decomposition α κ μ π τ η δ σ) :
    Function.Bijective d.seam ∧
      (∀ e : childSources d.child, d.seam (Sum.inl e) = Sum.inl (d.βsrc e)) ∧
      (∀ e : childSinks d.child, d.seam (Sum.inr e) = Sum.inr (d.βsnk e)) ∧
      (∀ x, d.kind (edgeOf (d.seam x)) = d.kind (edgeOf x)) :=
  ⟨d.seam.bijective, fun _ => rfl, fun _ => rfl, d.seam_preserves_kind⟩

end Decomposition

/-! ## Statement 2 — assembly (depth 1)

  A parent with a covering list of well-formed child `RecursiveSystem`s
  assembles into a `WellFormed` `RecursiveSystem`. The children may be
  unexpanded reference stubs (primitives) or expanded subtrees uniformly — the
  proof does not distinguish, which is exactly the claim that by-reference and
  in-place decomposition are the same mathematics. -/

variable [ActsOn α]

/-- Assemble a parent `ConcreteSystem` and a list of components (each mapped to
    a child `RecursiveSystem`) into one in-place `RecursiveSystem` node. -/
def assembleDepth1 (t : α) (σ' : ConcreteSystem α) (comps : List α)
    (childOf : α → RecursiveSystem α) : RecursiveSystem α :=
  .composite t σ' (comps.map childOf)

/-- **Statement 2 (depth 1).** If `comps` enumerates the parent's composition
    and every child sits at its component's identity and is well-formed, the
    assembled node is `WellFormed`. -/
theorem assembleDepth1_wellFormed (t : α) (σ' : ConcreteSystem α) (comps : List α)
    (childOf : α → RecursiveSystem α)
    (hcov : ∀ x ∈ σ'.composition, x ∈ comps)
    (hcomps : ∀ x ∈ comps, x ∈ σ'.composition)
    (hthing : ∀ x ∈ comps, (childOf x).thing = x)
    (hwf : ∀ x ∈ comps, (childOf x).WellFormed) :
    (assembleDepth1 t σ' comps childOf).WellFormed := by
  unfold assembleDepth1 RecursiveSystem.WellFormed
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact ⟨childOf x, List.mem_map.mpr ⟨x, hcov x hx, rfl⟩, hthing x (hcov x hx)⟩
  · intro c hc
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hc
    rw [hthing y hy]; exact hcomps y hy
  · intro c hc
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hc
    exact hwf y hy

/-- Corollary: decomposing exactly ONE component `c` (expanded to any
    well-formed `childRS`) while every other component stays a primitive
    reference stub yields a `WellFormed` assembly. The proof is indifferent to
    whether the `c` slot is expanded or a stub — the "same mathematics" claim,
    made concrete. -/
theorem decompose_one_wellFormed [DecidableEq α]
    (t c : α) (σ' : ConcreteSystem α) (comps : List α)
    (hcov : ∀ x ∈ σ'.composition, x ∈ comps)
    (hcomps : ∀ x ∈ comps, x ∈ σ'.composition)
    (childRS : RecursiveSystem α)
    (hchild_thing : childRS.thing = c)
    (hchild_wf : childRS.WellFormed) :
    (assembleDepth1 t σ' comps
      (fun x => if x = c then childRS else .primitive x)).WellFormed := by
  refine assembleDepth1_wellFormed t σ' comps _ hcov hcomps ?_ ?_
  · intro x _
    by_cases h : x = c
    · simp only [if_pos h]; rw [hchild_thing]; exact h.symm
    · simp only [if_neg h]; rfl
  · intro x _
    by_cases h : x = c
    · simp only [if_pos h]; exact hchild_wf
    · simp only [if_neg h]; exact RecursiveSystem.primitive_wellFormed x

/-! ## Deferred — NOT formalized here (conjectures)

  These are stated to record the honest boundary of what is proven; they are
  prose, not Lean `axiom`s, so they add nothing to the trusted base.

  * **Arbitrary-depth assembly.** `assembleDepth1_wellFormed` covers one
    decomposition edge. The general claim — a tree of flat 8-tuples linked by
    `Decomposition` edges, each child bridged `MobusSystem → ConcreteSystem`
    (`toBunge`), assembles by structural recursion into a `WellFormed`
    `RecursiveSystem` at every level, with each edge's `βsrc`/`βsnk` supplying
    the seam — is conjectured to follow by induction on the tree using
    `assembleDepth1_wellFormed` at each node. Deferred: the recursion carrier
    (a `Decomposition`-labelled tree) and the Mobus→Bunge lifting of the
    covering hypotheses.

  * **Verdict-preservation across levels.** Each level is validated at its own
    rung by construction; that the parent's lens verdicts are preserved under
    substitution of a verdict-passing child is conjectured, explicitly NOT a
    gate (decomposition-foundations.md §5).

  * **`T′` aggregation / `Δt` composition.** The dynamical face: recovering the
    parent's `T` at `comp` from the composition of the children's `T′`s, and
    cross-level `Δt` consistency. Deferred to the multi-timescale thread. -/

end Systems
