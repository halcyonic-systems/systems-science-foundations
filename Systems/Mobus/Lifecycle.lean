/-
  Systems/Mobus/Lifecycle.lean
  Closure of the 8-tuple under lawful change — the life-cycle paper's centre.

  Mobus's book-revisions gives the master equation

    S_{t+1} = S_t ∪ ⟨ΔS⟩

  and then five empty stage sections. Union is monotone, so it can only ADD:
  Decline (components leaving) and Dissolution (the boundary coming apart) are
  not expressible by it. His own ΔB = ⟨B \ {b_k}, B ∪ {b_new}⟩ already uses set
  difference — the notation was ahead of the master equation. The repair is an
  admissible-successor relation in place of union, and union survives as the
  Growth-regime special case.

  This file states the closure theorem:

    S ⊨ WF ∧ S' ∈ F(S) ⟹ S' ⊨ WF

  WHY WELL-FORMEDNESS IS REIFIED. `MobusSystem` carries its six coherence
  constraints as STRUCTURE FIELDS, so `F : MobusSystem → Set MobusSystem` makes
  closure true by construction and empty of content — every inhabitant is
  well-formed because the elaborator refused to build anything else. So the
  tuple is restated here as `PreTuple`, raw data with every law stripped, and
  well-formedness becomes a predicate on it. `wellFormed_toPre` and
  `toPre_toMobus` then pin the predicate to the structure in both directions,
  which is what stops a WEAKER `WellFormed` from making the closure theorem
  cheap. That pinning is load-bearing, not ceremonial: when SSF #31 added
  `interfaces_carry_flow` to `MobusSystem`, this file stopped compiling at
  `toMobus` until `WellFormed` was brought back into step.

  WHY A RELATION, NOT `kindCodomain .nondeterministic`. Dynamics/Transition.lean
  types the nondeterministic kind as `List X` — deliberately finite, so a final
  coalgebra exists. The life cycle's carrier is the 8-tuple, whose components are
  a `Set α`; demanding a `List` of successors would impose finiteness on the
  successor set for no ontological reason. `Step` is therefore a relation, and
  `F(S) = {S' | Step S S'}`. The finite `List` form is the computational
  restriction of this, not its definition.
-/

import Systems.Mobus.Tuple
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Insert
import Mathlib.Order.BooleanAlgebra.Set

namespace Systems

/-! ## The tuple as raw data -/

/-- A directed flow network with NO laws — `FlowNetwork` minus `edges_on` and
    `no_self_loops`. Stripping them is the point: they are what a transition
    could break, so they must be checkable rather than presupposed. -/
structure PreNetwork (α : Type*) (κ : Type*) where
  /-- The node set. -/
  nodes : Set α
  /-- The edge set, unconstrained. -/
  edges : Set (FlowEdge α κ)

/-- The laws `FlowNetwork` enforces by construction, as a predicate. -/
def PreNetwork.Lawful {α κ : Type*} (net : PreNetwork α κ) : Prop :=
  (∀ e ∈ net.edges, e.source ∈ net.nodes ∧ e.target ∈ net.nodes) ∧
  (∀ e ∈ net.edges, e.source ≠ e.target)

/-- The 8-tuple S = ⟨C, N, E, G, B, T, H, Δt⟩ as raw data: every coherence
    constraint of `MobusSystem` stripped out, and the two networks and the
    boundary flattened to their fields so nothing is enforced by a nested type.
    A `PreTuple` is a candidate system — it may fail to be one. -/
structure PreTuple (α : Type*) (κ : Type*) (μ : Type*)
    (π : Type*) (τ : Type*) (η : Type*) (δ : Type*) where
  /-- C -/
  components : Set α
  /-- N -/
  internalNetwork : PreNetwork α κ
  /-- E = ⟨O, M⟩, first half: the discrete objects O. -/
  envObjects : Set α
  /-- E = ⟨O, M⟩, second half: the milieu M. -/
  milieu : μ
  /-- G -/
  externalFlows : PreNetwork α κ
  /-- B = ⟨P, I⟩, first half: the boundary properties P. -/
  boundaryProps : π
  /-- B = ⟨P, I⟩, second half: the interface components I. -/
  interfaces : Set α
  /-- T -/
  transforms : τ
  /-- H -/
  history : η
  /-- Δt -/
  timeScale : δ

/-- `IsBipartiteFlow` restated over a bare edge set, since `PreNetwork` is not a
    `FlowNetwork`. The original only ever reads `net.edges`, so this is the same
    condition (`isBipartiteEdges_iff`). -/
def IsBipartiteEdges {α κ : Type*}
    (edges : Set (FlowEdge α κ)) (A B : Set α) : Prop :=
  ∀ e ∈ edges,
    (e.source ∈ A ∧ e.target ∈ B) ∨ (e.source ∈ B ∧ e.target ∈ A)

/-! ## Well-formedness as a predicate -/

/-- `WF` — the well-formedness predicate. Exactly the content `MobusSystem`
    enforces by construction: the two networks' own laws, plus the six
    coherence constraints. This is the invariant the life cycle preserves.

    Field names deliberately match `MobusSystem`'s constraint fields, so the
    correspondence is readable rather than argued. -/
structure WellFormed {α κ μ π τ η δ : Type*}
    (p : PreTuple α κ μ π τ η δ) : Prop where
  /-- N is a lawful graph. -/
  internal_lawful : p.internalNetwork.Lawful
  /-- G is a lawful graph. -/
  external_lawful : p.externalFlows.Lawful
  /-- N's vertex set is exactly C. -/
  network_components : p.internalNetwork.nodes = p.components
  /-- C ∩ O = ∅. -/
  disjoint : p.components ∩ p.envObjects = ∅
  /-- I ⊆ C. -/
  interfaces_sub : p.interfaces ⊆ p.components
  /-- Every external flow crosses the boundary. -/
  bipartite : IsBipartiteEdges p.externalFlows.edges p.envObjects p.interfaces
  /-- G's nodes lie in O ∪ I. -/
  externalFlows_nodes : p.externalFlows.nodes ⊆ p.envObjects ∪ p.interfaces
  /-- Every interface carries at least one external flow (SSF #31). Added when
      `MobusSystem` gained `interfaces_carry_flow`: adequacy failed to compile
      until `WellFormed` matched, which is the "no weaker" direction working. -/
  interfaces_carry_flow :
    InterfacesCarryEdges p.externalFlows.edges p.interfaces

/-! ## Adequacy — the predicate is exactly the structure

    Without this, nothing stops `WellFormed` from being a weaker predicate that
    makes the closure theorem easy. Both directions are needed: `toPre` says WF
    is no STRONGER than the structure, `toMobus` says it is no WEAKER.
-/

/-- Forget the constraints: every `MobusSystem` has an underlying `PreTuple`. -/
def MobusSystem.toPre {α κ μ π τ η δ : Type*}
    (sys : MobusSystem α κ μ π τ η δ) : PreTuple α κ μ π τ η δ where
  components := sys.components
  internalNetwork := ⟨sys.internalNetwork.nodes, sys.internalNetwork.edges⟩
  envObjects := sys.environment.objects
  milieu := sys.environment.milieu
  externalFlows := ⟨sys.externalFlows.nodes, sys.externalFlows.edges⟩
  boundaryProps := sys.boundary.properties
  interfaces := sys.boundary.interfaces
  transforms := sys.transforms
  history := sys.history
  timeScale := sys.timeScale

/- PROOF TARGET: The underlying raw tuple of any Mobus system is well-formed.

   MATHEMATICAL INTENT:
   WF is no stronger than what the type already enforces. Half of adequacy.

   AVAILABLE TOOLS:
   `MobusSystem` fields (`network_components`, `disjoint`, `interfaces_sub`,
   `bipartite`, `externalFlows_nodes`), `FlowNetwork.edges_on`,
   `FlowNetwork.no_self_loops`, `IsBipartiteFlow` (definitionally
   `IsBipartiteEdges` on `.edges`).

   DOES NOT COUNT:
   - proving it for a `WellFormed` that omits a constraint
   - `decide` on a concrete instance

   STRATEGY HINT: constructor, then each field from the corresponding
   `MobusSystem` field. Should be near-mechanical.
-/
theorem wellFormed_toPre {α κ μ π τ η δ : Type*}
    (sys : MobusSystem α κ μ π τ η δ) : WellFormed sys.toPre where
  internal_lawful :=
    ⟨sys.internalNetwork.edges_on, sys.internalNetwork.no_self_loops⟩
  external_lawful :=
    ⟨sys.externalFlows.edges_on, sys.externalFlows.no_self_loops⟩
  network_components := sys.network_components
  disjoint := sys.disjoint
  interfaces_sub := sys.interfaces_sub
  bipartite := sys.bipartite
  externalFlows_nodes := sys.externalFlows_nodes
  interfaces_carry_flow := sys.interfaces_carry_flow

/- PROOF TARGET: A well-formed raw tuple can be rebuilt as a Mobus system, and
   rebuilding recovers the same raw data.

   MATHEMATICAL INTENT:
   WF is no weaker than what the type enforces — a WF PreTuple omits nothing the
   structure needs. This is the direction that makes a weakened WF impossible to
   sneak past: a missing constraint would leave this construction unbuildable.

   AVAILABLE TOOLS:
   `WellFormed` fields; `FlowNetwork` and `MobusBoundary`/`MobusEnvironment`
   constructors; `PreNetwork.Lawful` unfolds to the two `FlowNetwork` laws.

   DOES NOT COUNT:
   - returning a DIFFERENT system that happens to be well-formed; the round-trip
     `toPre_toMobus` is what forbids this
   - adding a hypothesis beyond `WellFormed p`

   STRATEGY HINT: build the two `FlowNetwork`s from `Lawful`, then the tuple;
   the round trip should be `rfl` if the fields are assembled in order.
-/
def PreTuple.toMobus {α κ μ π τ η δ : Type*}
    (p : PreTuple α κ μ π τ η δ) (h : WellFormed p) :
    MobusSystem α κ μ π τ η δ where
  components := p.components
  internalNetwork :=
    { nodes := p.internalNetwork.nodes
      edges := p.internalNetwork.edges
      edges_on := h.internal_lawful.1
      no_self_loops := h.internal_lawful.2 }
  environment := { objects := p.envObjects, milieu := p.milieu }
  externalFlows :=
    { nodes := p.externalFlows.nodes
      edges := p.externalFlows.edges
      edges_on := h.external_lawful.1
      no_self_loops := h.external_lawful.2 }
  boundary := { properties := p.boundaryProps, interfaces := p.interfaces }
  transforms := p.transforms
  history := p.history
  timeScale := p.timeScale
  network_components := h.network_components
  disjoint := h.disjoint
  interfaces_sub := h.interfaces_sub
  bipartite := h.bipartite
  externalFlows_nodes := h.externalFlows_nodes
  interfaces_carry_flow := h.interfaces_carry_flow

theorem toPre_toMobus {α κ μ π τ η δ : Type*}
    (p : PreTuple α κ μ π τ η δ) (h : WellFormed p) :
    (p.toMobus h).toPre = p := rfl

/-! ## The admissible transitions -/

/-- A Growth edit: introduce a component. It joins C and becomes a vertex of N
    with no flows yet. Mobus's ∪ update, as one primitive. -/
def PreTuple.addComponent {α κ μ π τ η δ : Type*}
    (p : PreTuple α κ μ π τ η δ) (a : α) : PreTuple α κ μ π τ η δ :=
  { p with
    components := insert a p.components
    internalNetwork :=
      { p.internalNetwork with nodes := insert a p.internalNetwork.nodes } }

/-- A Decline edit: remove a component, together with every internal flow
    incident to it. Taking the incident edges with it is not a convenience —
    leaving them would strand edges on a missing vertex, which is precisely the
    kind of breakage `WF` exists to forbid.

    This is the edit `S_{t+1} = S_t ∪ ⟨ΔS⟩` cannot express. -/
def PreTuple.removeComponent {α κ μ π τ η δ : Type*}
    (p : PreTuple α κ μ π τ η δ) (a : α) : PreTuple α κ μ π τ η δ :=
  { p with
    components := p.components \ {a}
    internalNetwork :=
      { nodes := p.internalNetwork.nodes \ {a}
        edges := {e ∈ p.internalNetwork.edges | e.source ≠ a ∧ e.target ≠ a} } }

/-- The admissible-successor relation `F`: one lawful edit. `F(S) = {S' | Step S S'}`.

    Each constructor carries the side condition that makes the edit lawful, and
    those side conditions are the whole content of the closure theorem. -/
inductive Step {α κ μ π τ η δ : Type*} :
    PreTuple α κ μ π τ η δ → PreTuple α κ μ π τ η δ → Prop where
  /-- Growth: add a component that is not an environmental object. -/
  | grow (p : PreTuple α κ μ π τ η δ) (a : α) (h : a ∉ p.envObjects) :
      Step p (p.addComponent a)
  /-- Decline: remove a component that is not an interface. Removing an
      interface additionally requires retracting its external flows — a
      separate edit, deliberately not in this increment. -/
  | decline (p : PreTuple α κ μ π τ η δ) (a : α) (h : a ∉ p.interfaces) :
      Step p (p.removeComponent a)

/-- Reachability: `F`'s reflexive-transitive closure — a life-cycle trajectory. -/
abbrev Reaches {α κ μ π τ η δ : Type*} :
    PreTuple α κ μ π τ η δ → PreTuple α κ μ π τ η δ → Prop :=
  Relation.ReflTransGen Step

/-! ## Closure — the paper's §4 -/

/- PROOF TARGET: Adding a non-environmental component preserves well-formedness.

   MATHEMATICAL INTENT:
   The Growth half of closure.

   AVAILABLE TOOLS:
   `Set.insert_inter_distrib`? — check; more likely `Set.eq_empty_iff_forall_not_mem`
   and case analysis on `Set.mem_insert_iff`. `Set.subset_insert`.

   DOES NOT COUNT:
   - dropping the `a ∉ p.envObjects` side condition into the conclusion
   - proving it only for `a ∈ p.components` (where the edit is a no-op)

   STRATEGY HINT: constructor; `disjoint` is the only field needing the
   hypothesis; `network_components` should follow by congruence on `insert`.
-/
theorem addComponent_wellFormed {α κ μ π τ η δ : Type*}
    {p : PreTuple α κ μ π τ η δ} (h : WellFormed p) {a : α}
    (ha : a ∉ p.envObjects) : WellFormed (p.addComponent a) where
  internal_lawful :=
    ⟨fun e he =>
      ⟨Set.mem_insert_of_mem _ (h.internal_lawful.1 e he).1,
       Set.mem_insert_of_mem _ (h.internal_lawful.1 e he).2⟩,
     h.internal_lawful.2⟩
  external_lawful := h.external_lawful
  network_components := by
    show insert a p.internalNetwork.nodes = insert a p.components
    rw [h.network_components]
  disjoint := by
    show insert a p.components ∩ p.envObjects = ∅
    rw [Set.insert_inter_of_notMem ha, h.disjoint]
  interfaces_sub := h.interfaces_sub.trans (Set.subset_insert _ _)
  bipartite := h.bipartite
  externalFlows_nodes := h.externalFlows_nodes
  interfaces_carry_flow := h.interfaces_carry_flow

/- PROOF TARGET: Removing a non-interface component (with its incident internal
   flows) preserves well-formedness.

   MATHEMATICAL INTENT:
   The Decline half of closure — the half Mobus's ∪ cannot reach. This is the
   theorem that makes the five stage sections writable.

   AVAILABLE TOOLS:
   `WellFormed` fields; `Set.diff_subset`; `Set.mem_diff`; the filtered edge set
   is a subset of the original so `no_self_loops` transfers.

   DOES NOT COUNT:
   - preserving WF by making the edit a no-op (e.g. requiring a ∉ p.components)
   - dropping the incident-edge deletion and adding a hypothesis that no edges
     touch `a` — that is a weaker, easier theorem about a different edit
   - leaving G's constraints unexamined because G's data is untouched: the
     constraints mention `interfaces` and `envObjects`, so they must be rechecked

   STRATEGY HINT: constructor; `internal_lawful` needs the filter condition to
   land endpoints in `nodes \ {a}`; the external three are untouched data but
   must still be discharged.
-/
theorem removeComponent_wellFormed {α κ μ π τ η δ : Type*}
    {p : PreTuple α κ μ π τ η δ} (h : WellFormed p) {a : α}
    (ha : a ∉ p.interfaces) : WellFormed (p.removeComponent a) where
  internal_lawful :=
    ⟨fun e he =>
      ⟨⟨(h.internal_lawful.1 e he.1).1, by simpa using he.2.1⟩,
       ⟨(h.internal_lawful.1 e he.1).2, by simpa using he.2.2⟩⟩,
     fun e he => h.internal_lawful.2 e he.1⟩
  external_lawful := h.external_lawful
  network_components := by
    show p.internalNetwork.nodes \ {a} = p.components \ {a}
    rw [h.network_components]
  disjoint :=
    Set.subset_eq_empty
      (Set.inter_subset_inter_left _ Set.diff_subset) h.disjoint
  interfaces_sub := fun x hx =>
    ⟨h.interfaces_sub hx, fun hxa => ha (hxa ▸ hx)⟩
  bipartite := h.bipartite
  externalFlows_nodes := h.externalFlows_nodes
  interfaces_carry_flow := h.interfaces_carry_flow

/- PROOF TARGET: every single admissible step preserves well-formedness.

   MATHEMATICAL INTENT: one-step closure, S ⊨ WF ∧ S' ∈ F(S) ⟹ S' ⊨ WF.

   DOES NOT COUNT: a `Step` typed on `MobusSystem` instead of `PreTuple` —
   that makes this `fun _ h => h` and asserts nothing.

   STRATEGY HINT: `cases` on the step, then the two lemmas above.
-/
theorem Step.preserves_wellFormed {α κ μ π τ η δ : Type*}
    {p p' : PreTuple α κ μ π τ η δ} (hstep : Step p p') (h : WellFormed p) :
    WellFormed p' := by
  cases hstep with
  | grow a hp => exact addComponent_wellFormed h hp
  | decline a hp => exact removeComponent_wellFormed h hp

/- PROOF TARGET: THE CLOSURE THEOREM. Well-formedness persists along any
   life-cycle trajectory, of any length.

   MATHEMATICAL INTENT:
   The paper's §4 and its centre. "The 8-tuple is closed under the transitions
   that define a life cycle" — the invariant that persists (WF) and the class of
   transitions that preserve it (Step), composed over arbitrarily many steps.
   This is what fills the five empty stage sections: each stage is a restriction
   on which edits F admits, and every one of them inherits this theorem.

   AVAILABLE TOOLS: `Relation.ReflTransGen.head_induction_on` or plain
   induction on `ReflTransGen`; `Step.preserves_wellFormed`.

   DOES NOT COUNT:
   - the one-step version restated (`Step.preserves_wellFormed` is not this)
   - a trajectory relation that cannot decrease components — then the theorem
     holds of a Growth-only regime and says nothing about a life CYCLE

   STRATEGY HINT: induction on `Reaches`.
-/
theorem wellFormed_of_reaches {α κ μ π τ η δ : Type*}
    {p p' : PreTuple α κ μ π τ η δ} (h : WellFormed p) (hr : Reaches p p') :
    WellFormed p' := by
  induction hr with
  | refl => exact h
  | tail _ hstep ih => exact hstep.preserves_wellFormed ih

/-! ## Mobus's union equation, and why it cannot reach its own stages -/

/-- A transition regime is additive when no successor ever loses a component.
    `S_{t+1} = S_t ∪ ⟨ΔS⟩` is exactly this condition. -/
def Additive {α κ μ π τ η δ : Type*}
    (R : PreTuple α κ μ π τ η δ → PreTuple α κ μ π τ η δ → Prop) : Prop :=
  ∀ p p', R p p' → p.components ⊆ p'.components

/- PROOF TARGET: under an additive regime, no component is ever lost along a
   trajectory of any length.

   MATHEMATICAL INTENT:
   Monotonicity is inherited by the whole trajectory, not just one step. This is
   the precise sense in which Mobus's master equation cannot express Decline or
   Dissolution: not "it is hard to", but "no trajectory it generates ever drops
   a component." The stage sections are empty for a formal reason.

   AVAILABLE TOOLS: `Relation.ReflTransGen` induction; `Set.Subset.trans`.

   DOES NOT COUNT: the one-step statement (that is `Additive` itself).

   STRATEGY HINT: induction on `ReflTransGen`, `subset_trans` at the step.
-/
theorem additive_components_monotone {α κ μ π τ η δ : Type*}
    {R : PreTuple α κ μ π τ η δ → PreTuple α κ μ π τ η δ → Prop}
    (hR : Additive R) {p p' : PreTuple α κ μ π τ η δ}
    (hr : Relation.ReflTransGen R p p') : p.components ⊆ p'.components := by
  induction hr with
  | refl => exact subset_rfl
  | tail _ hstep ih => exact ih.trans (hR _ _ hstep)

/-- Growth alone: the additive sub-regime of `Step`, i.e. Mobus's ∪. -/
inductive GrowthStep {α κ μ π τ η δ : Type*} :
    PreTuple α κ μ π τ η δ → PreTuple α κ μ π τ η δ → Prop where
  | grow (p : PreTuple α κ μ π τ η δ) (a : α) (h : a ∉ p.envObjects) :
      GrowthStep p (p.addComponent a)

/- PROOF TARGET: the Growth regime is additive.

   MATHEMATICAL INTENT: union IS a regime of F — the generous reading. Mobus's
   equation is not wrong; it is F restricted to one of five stages.

   DOES NOT COUNT: proving it of `Step` (false — that is the next theorem).

   STRATEGY HINT: cases; `Set.subset_insert`.
-/
theorem growthStep_additive {α κ μ π τ η δ : Type*} :
    Additive (@GrowthStep α κ μ π τ η δ) := by
  intro p p' hstep
  cases hstep with
  | grow a _ => exact Set.subset_insert a p.components

/-! ## Non-vacuity — the witness

    Every theorem above would still be true of a regime that never removes
    anything, and then the closure theorem would be a statement about Growth
    wearing a life-cycle name. The sketch pre-registered that outcome as not
    counting, so it is checked here rather than asserted.

    `witness` has a real internal flow 0 → 1, so declining component 0 must
    retract an edge as well as a vertex — the case where `internal_lawful`
    would break if the edit were defined carelessly.
-/

/-- Two components, one internal flow 0 → 1, no environment and no interfaces. -/
def witness : PreTuple ℕ Unit Unit Unit Unit Unit Unit where
  components := {0, 1}
  internalNetwork := ⟨{0, 1}, {⟨0, 1, ()⟩}⟩
  envObjects := ∅
  milieu := ()
  externalFlows := ⟨∅, ∅⟩
  boundaryProps := ()
  interfaces := ∅
  transforms := ()
  history := ()
  timeScale := ()

theorem witness_wellFormed : WellFormed witness where
  internal_lawful := by
    constructor
    · rintro e rfl; simp [witness]
    · rintro e rfl; simp
  external_lawful := by constructor <;> (intro e he; simp [witness] at he)
  network_components := rfl
  disjoint := Set.inter_empty _
  interfaces_sub := Set.empty_subset _
  bipartite := by intro e he; simp [witness] at he
  externalFlows_nodes := Set.empty_subset _
  interfaces_carry_flow := by intro i hi; simp [witness] at hi

/-- Declining component 0 is an admissible step from the witness. -/
theorem witness_declines : Step witness (witness.removeComponent 0) :=
  Step.decline witness 0 (by simp [witness])

/-- The successor is still well-formed — closure, on a concrete trajectory. -/
theorem witness_successor_wellFormed :
    WellFormed (witness.removeComponent 0) :=
  witness_declines.preserves_wellFormed witness_wellFormed

/-- A component really is gone: the step is not a no-op dressed as a removal. -/
theorem witness_lost_component :
    (0 : ℕ) ∈ witness.components ∧
    (0 : ℕ) ∉ (witness.removeComponent 0).components := by
  refine ⟨by simp [witness], ?_⟩
  simp [PreTuple.removeComponent]

/-- The incident flow went with it — `N` did not keep an edge on a dead vertex. -/
theorem witness_edge_retracted :
    (witness.removeComponent 0).internalNetwork.edges = ∅ := by
  ext e
  simp only [PreTuple.removeComponent, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro rfl
  simp

/-- THE SEPARATION: `Step` is not additive. So `wellFormed_of_reaches` is a
    statement about trajectories that genuinely lose structure, and Mobus's ∪
    is strictly weaker than `F` — it cannot generate this one step. -/
theorem step_not_additive :
    ¬ Additive (@Step ℕ Unit Unit Unit Unit Unit Unit) := by
  intro hadd
  exact witness_lost_component.2
    (hadd _ _ witness_declines witness_lost_component.1)

end Systems
