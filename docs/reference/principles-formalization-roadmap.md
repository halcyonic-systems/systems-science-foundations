# Principles Formalization Roadmap

*Axiomatizing Mobus's 12 principles of systems science in Lean 4*

**Created**: 2026-05-20
**Companion**: `strategy/research/formalization-manifesto.md` (the "why")
**Plain English summary**: `docs/reference/principles-formalization-companion.md` (axiom candidates, what each formalization means, what's deferred)
**Prerequisite**: K ≅ **2** common core theorem (complete, zero `sorry`s)
**Design principle**: Same as categorification roadmap — don't formalize for its own sake. Each formalization must answer a question that prose cannot.

**Methodological commitment**: For each principle, explore *multiple* candidate formalizations from different mathematical foundations before committing to one. The workflow is: **deep source reading (Bunge, Mobus, Klir) → literature survey (Zotero, external) → multiple candidate sketches → prototype most promising → certify in Lean**. Premature commitment to one approach per principle is the main risk. The intellectual work is choosing the right formalization, not executing a predetermined one.

**Session close-out**: After every formalization session: (1) axiom table in companion doc — FIRST, plain English, (2) per-principle "What we proved" / "What we found" sections, (3) tasknote checkboxes, (4) this roadmap's assessment table, (5) session file accomplishments. The axiom table is the primary deliverable — if it's stale, the work hasn't been communicated.

---

## Assessment Table

| # | Principle | Current State | Mathematical Domain | Amenability | Dependencies | Tier |
|---|-----------|--------------|-------------------|-------------|-------------|------|
| 1 | Systemness | **Complete** | Inductive types, closure properties | HIGH | None | 1 |
| 2 | Hierarchy | **Complete** (conditional on Dynamics #4 for full Simon) | Partial orders, interaction strength | HIGH | #1 | 1 |
| 3 | Networks | **Done** | Graph theory, category theory | — | — | — |
| 4 | Dynamics | **Complete** (structural — quantitative convergence deferred) | Dynamical systems, equilibrium, flows, timescale decomposition | — | #3 | 2 |
| 5 | Complexity | **Derived** (structural part reduces to #1+#2+#3) | Equivalence relations, set operations | — | #1, #2, #3 | 1 |
| 6 | Evolution | Not formalized | Fitness landscapes, temporal logic | LOW | #4, #5 | 3 |
| 7 | Information | **Theorem** (layered core — Information.lean; genus = difference-that-makes-a-difference, Hartley nonspecificity, Shannon as bounded special case `entropy ≤ hartley`; mutual-info/capacity + semantic layer deferred) | Information theory, channel capacity | — | #3 | 2 |
| 8 | Governance | **Axiom** + lens bridge (homeostat = lens + setPoint, Conant-Ashby skeleton) | Control theory, feedback, lenses, fixed points | — | #4, #3 | 2 |
| 9 | Internal Models | **Theorem** (InternalModel.lean — simulation lifts to all horizons; → Conant-Ashby) | Simulation relation, semiconjugacy, induction | — | #4, #8 | 2 |
| 10 | Self-Models | **Theorem** (tractable core — SelfModel.lean; diagonal of #9, self-anticipation, accurate set invariant; faithful-existence/Lawvere deferred) | Fixed-point theory, self-reference | — | #9 | 3 |
| 11 | Understandability | Not formalized | Rosen modeling, Kolmogorov, epistemology | MEDIUM | #5, #9 | 2-3 |
| 12 | Improvability | Not formalized | Fitness landscapes, design theory, agency | MEDIUM | #6, #9, #11 | 2-3 |

---

## Detailed Assessment

### Principle 1: Systemness

**Mobus**: "Bounded networks of relations among parts constitute a holistic unit. Systems interact with other systems, forming yet larger systems. The Universe is composed of systems of systems."

**Current Lean state**: `System.lean` defines `ConcreteSystem ⟨C, E, S⟩` with 5 coherence constraints. `Level.lean` has `RecursiveComponent` (inductive type guaranteeing decomposition terminates). `Assembly.lean` has Bunge's assembly definition. But the systemness *predicate* — the claim that every component is either atomic or itself a system — is implicit in the type structure, not stated as an axiom with consequences.

**What formalization would mean**:
- `IsSystem` predicate with explicit closure properties
- Theorem: subsystem of a system is a system (closure under decomposition)
- Theorem: composition of interacting systems is a system (closure under composition)
- Distinction between systemness and mere aggregation (Mobus's "organized vs. heaped")
- Connect `RecursiveComponent` to `ConcreteSystem` formally (currently separate types)

**Approach**: Sets/inductive types. No categories needed.
**Effort**: 2 sessions (actual). Composition closure completed 2026-05-24. Finding: the CES construction is unconditionally valid — neither disjointness nor interaction hypothesis is needed for coherence proofs. The hypotheses add physical content, not mathematical necessity.
**Risk**: Resolved.

---

### Principle 2: Hierarchy

**Mobus**: "Systems are processes organized in structural and functional hierarchies... The next higher layer consists of subsystems composed of components from the lower layer in which component interactions within the subsystem are stronger than interactions between components in other subsystems."

**Current Lean state**: `Level.lean` has `LevelStructure` (ordered family of nonempty sets with precedence), `LevelPrecedes` (composition relation between levels), `RecursiveComponent` with `depth` and `atomicCount`, `Ancestor`/`ancestry`/`progeny`/`lineage` relations. Showcase theorem #5: ancestry is a strict partial order.

**What's missing**:
- **Time-scale separation**: Mobus explicitly ties hierarchy to time scales — lower levels are faster. Currently `Tuple.lean` has `timeScale : δ` as a single parameter, not a per-level constraint.
- **Near-decomposability** (Simon): Interaction strength within modules exceeds interaction strength between modules. This is the formal criterion that distinguishes hierarchy from arbitrary nesting.
- **Functional vs. structural hierarchy**: `LevelStructure` captures structural hierarchy (composition). Functional hierarchy (governance layers, HCGS) is not formalized.

**What formalization would mean**:
- `TimeScaleSeparation` structure: monotone map from levels to time scales
- `NearDecomposable` structure: within-module interaction > between-module interaction
- Theorem: near-decomposability implies time-scale separation (Simon's conjecture, formalizable)
- Connect `LevelStructure` to `SubsystemCategory` (hierarchical levels as a thin category)

**Approach**: Sets first (time-scale separation as a monotone function on the level poset). Categorical upgrade later if it reveals new theorems about functorial preservation of hierarchy.
**Effort**: 2 sessions (actual). Conditional time-scale separation completed 2026-05-24. The theorem names Simon's implicit assumption (`StrictAnti f`: stronger interaction → shorter time scale) and proves that under this assumption alone, near-decomposability implies time-scale separation. Full unconditional version awaits Dynamics (#4).
**Risk**: Resolved for conditional version. Full version depends on Dynamics (#4).

---

### Principle 3: Networks — DONE

**Current Lean state**: `FlowNetwork.lean` (directed capacity-labeled graphs, source/sink/internal classification, successors/predecessors), `Bond.lean` (ActsOn relation, bonded pairs), `Interface.lean` (bipartite flow property). Fully formalized. No further work needed at this tier.

---

### Principle 4: Dynamics — COMPLETE (structural)

**Mobus**: "Systems are dynamic on multiple time scales."

**Current Lean state** (482 lines, zero sorry): `Dynamics.lean` contains the full structural axiomatization. `DynamicSystem` (ConcreteSystem + law : S → S) with composition as product state spaces and both projection theorems. `CoupledDynamicSystem` (mutual influence) with `toCoupled` embedding from independent dynamics. `IsEquilibrium` with product equilibria, coupled-iff-fixed biconditional, independent-implies-coupled, and iteration stability. `Flow` (semigroup action on state space, `AddMonoid T`) with composition and projection. `TimescaleDecomposition` with fast/slow separation around a reference equilibrium — 5 theorems proving fast dynamics recovers subsystem laws and the reference equilibrium is a fixed point of both fast and slow. `InteractionDynamicsBridge` completes Simon's conditional from Level.lean. `DynamicSystem.evolve` and `trajectory` connect to State.lean's history type. The Lens Bridge (Lens.lean) connects dynamics to categorical cybernetics via `Homeostat.toLens`.

**What's formalized** (7 axiom-table entries, all proved):
- State: DynamicSystem structure
- Composition: product state spaces, projection preservation
- Coupling: CoupledDynamicSystem, embedding from independent
- Equilibrium: product, coupled ↔ fixed, independent → coupled, iterate stability
- Flow: semigroup action, composition, projection
- Timescale: decomposition structure, fast/slow equilibrium, independent recovery
- Bridge: InteractionDynamicsBridge → Simon's time-scale separation

**What's deferred** (research-level extensions, not axiomatization gaps):
- Quantitative convergence: requires metric on state space and convergence rates
- Stochastic transitions: requires measure theory / probability
- Input-dependent evolution: extends DynamicSystem to open systems
- Time-varying flows: needed for Conant-Ashby full theorem

**Effort**: Completed across W21 sessions (dynamics full formalization 2026-05-24, bridge infrastructure earlier in week).
**Risk**: Resolved.

---

### Principle 5: Complexity — DERIVED (theorem, not axiom)

**Mobus**: "Systems exhibit various kinds and levels of complexity."

**Current Lean state**: `Complexity.lean` proves derivability. `SameKind` equivalence (components with identical interaction profiles are "of the same kind") derives from ActsOn alone. Structural complexity measures — component count, component-kind diversity, network density, hierarchical depth — all derive from #1+#2+#3. Simonian state-space reduction bridges #1+#2 to #4. Behavioral complexity is Mobus's own open problem, not part of the stated principle.

**Key result**: Complexity is NOT an independent axiom. The 12 reduce by at least 1 (Finding 4, Finding 5 in companion doc). The file compiles with only Core imports — placement in `Systems/Core/` IS the derivability argument.

**Effort**: Completed 2026-05-22 (single session).
**Risk**: Resolved.

---

### Principle 6: Evolution

**Mobus**: "Systems evolve to accommodate long-term changes in their environments."

**Current Lean state**: Not formalized. The `Δt` field is parametric; there is no concept of fitness, selection, or environmental pressure.

**What formalization would mean**:
- Fitness function over system configurations
- Selection dynamics: systems with higher fitness persist; others don't
- Accommodation: system structure changes in response to persistent environmental changes
- Distinction between adaptation (reversible, within-lifetime) and evolution (irreversible, across generations)

**Approach**: This likely needs dynamical systems formalism (Principle 4 as prerequisite) plus additional structure for selection and variation. Possibly category-theoretic from the start — rewriting systems or temporal type theory.
**Effort**: Research-level. Multiple sessions, unclear endpoint.
**Risk**: High — "evolution" is one of the most overloaded terms in science. Finding the right level of abstraction is the core challenge. Defer until Tiers 1-2 are solid.

---

### Principle 7: Information & Knowledge

**Mobus**: "Systems encode knowledge and receive and send information."

**✓ RESOLVED — layered core (2026-06-08, `Systems/Core/Information.lean`).** Formalized in three layers, each requiring strictly more structure than the last, so that **Shannon's communication-statistics is forced to be a bounded special case by the dependency graph, not asserted** (Klir's Generalized-Information-Theory stance):

1. **Genus (probability-free)** — information = *a difference that makes a difference* (Bateson). A `Channel` is a message-driven update `recv : S → M → S`; a message is `Informative` at `s` iff `recv s m ≠ s`. Knowledge is the state it updates — the internal model of #9 (`InternalModel.toChannel` exhibits the autonomous model as the input-free channel; `noninformative_iff_equilibrium` ties the genus to Dynamics #4).
2. **Hartley nonspecificity (set-based, still probability-free)** — `hartley A = log |A|`, the amount that could be resolved with no distribution. `Channel.nonspecificity` is the Hartley measure of a channel's reachable set; it bottoms out to 0 exactly when nothing is informative.
3. **Shannon (probability-based, the special case)** — reusing `entropy` from `GoodRegulator.lean`, the headline refinement `entropy_le_hartley_univ`: entropy is bounded **above** by Hartley, with equality only at the uniform distribution (`entropy_uniform_eq_log_card`), proved by Jensen on the concave `negMulLog`. Adding a distribution to the prob-free ceiling can only lower the measure.

Theorem-tier, no new axiom. **Deferred (research-level)**: mutual information, the data-processing inequality, operational channel capacity (sup of mutual information over input distributions), and the **semantic / viability layer** above the genus — meaning and goal-relevance, refining the genus by a set-point à la Governance #8. The top of the stack is left deliberately open per the long-term aim of a conception of information not constrained by Shannon's communication statistics.

  **FlowNetwork bridge (the distinctively-Mobus next step, carried over from the 6/09 scaffold)**: the current `Channel` genus is abstract. `Systems/Mobus/FlowNetwork.lean` carries a *parametric edge capacity κ*. The payoff that makes this "#7 Information" rather than generic info theory is to frame a flow edge as a channel and relate κ to channel capacity — a bridge theorem that a flow network carries information bounded by its capacities, connecting BERT's flow infrastructure to the information measures. Even a structural statement (definition + one capacity bound) would earn the Mobus connection; the full operational-capacity theorem can come later.

**Risk**: was MEDIUM (contested information/knowledge boundary); the layered architecture resolved it by making the genus probability-free and subordinating Shannon, rather than committing to a single measure.

---

### Principle 8: Governance / Regulation

**Mobus**: "Systems have governance subsystems to achieve stability."

**Current Lean state**: Not formalized. But the categorification roadmap Phase 4 plans to formalize Joslyn's Control1/Control2 hierarchy, which IS the governance principle in categorical form. `ShapeJoslyn` (the only cyclic shape category) encodes the feedback structure.

**What formalization would mean**:
- `GovernanceSubsystem` structure: a distinguished subsystem whose outputs regulate other subsystems' behavior
- Feedback loop: governance subsystem receives information about system state and acts to maintain stability
- HCGS (Hierarchical Cybernetic Governance System): Strategic → Coordination → Operational layers
- Stability: governance maintains system state within a viable region (Ashby's requisite variety as a theorem)

**Approach**: Sets first for the basic governor-regulated decomposition. Categories for the feedback structure — traced monoidal categories or operads. This aligns with categorification roadmap Phase 4 (Joslyn extension). The Joslyn formalization IS the Governance formalization.
**Effort**: 3-5 sessions. Depends on resolving the Joslyn cyclic-category problem (identified as open in the categorification roadmap).
**Risk**: Medium — the cyclic feedback structure generates infinite hom-sets, which is why Joslyn is the only tradition not yet fully integrated into the categorification program.

---

### Principle 9: Internal Models

**✓ RESOLVED (2026-06-07, `Systems/Core/InternalModel.lean`).** Formalized the tractable core — the simulation relation — as the roadmap predicted. `InternalModel R S` carries a model map + internal/system dynamics with a one-step commuting square (`Function.Semiconj`). Main theorem `InternalModel.tracks`: one-step simulation lifts to every horizon (`model (internalDyn^[n] r) = systemDyn^[n] (model r)`) by induction — so **anticipation is structural, not an extra feature**. `InternalModel.toConantAshby` bridges to #8 (the model map is the good-regulator homomorphism). Theorem-tier: no new axiom (built from Dynamics #4). The anticipatory/stochastic versions remain future work; the deterministic simulation core is done. **Self-Models (#10) is now unblocked** — it's the S = R case.

**Mobus**: "Systems contain models of other systems (e.g., simple built-in protocols for interaction with other systems and up to complex anticipatory models)."

**Current Lean state**: Not formalized. The `ShapeComparison_Myers.lean` file shows that the Mobus shape captures `expose` (observation) but not `update` (action) — the statics/dynamics boundary.

**What formalization would mean**:
- A system S₁ contains a model of system S₂ iff S₁ has a subsystem whose state space is isomorphic to (a projection of) S₂'s state space
- Simulation relation: the model tracks the modeled system under some dynamics
- Anticipatory models: the model can predict future states (requires dynamics, Principle 4)
- Myers's lens formalism as the categorical structure: `get` (observe) and `put` (update)

**Approach**: Sets first for the simulation relation (state-space homomorphism). Lenses for the categorical version. This is where Myers's contribution becomes essential — the Mobus formalization captures structure but not the expose/update dynamics that internal models require.
**Effort**: 3-5 sessions. Research-level for the anticipatory version.
**Risk**: High for the full version. The basic simulation relation is tractable; anticipatory models require Dynamics (#4) to be formalized first.

---

### Principle 10: Self-Models

**Mobus**: "Sufficiently complex, adaptive systems can contain self-models."

**✓ RESOLVED — tractable core (2026-06-08, `Systems/Core/SelfModel.lean`).** Formalized the self-model as the **diagonal case of Internal Models (#9)**: one state space `S` with `selfModel : S → S` simulating the system's own dynamics — exactly `InternalModel S S` with `internalDyn = systemDyn = dyn`. `SelfModel.toInternalModel` makes the reuse explicit, so every #9 result transfers: `SelfModel.tracks` gives **self-anticipation** (a correct one-step self-model predicts the system's own future at every horizon), and `equilibrium_image` carries fixed points through the self-model. Two findings beyond instantiation: (1) **existence is trivial** — the identity self-models any system (`SelfModel.trivial`), so the content is faithfulness, not existence; (2) **self-consistency is dynamics-invariant** — a state the model represents as itself (`selfModel s = s`) stays so under the dynamics (`accurate_invariant`), the self-reference loop closing into itself without heavy machinery. Theorem-tier, no new axiom (reuses #9).

**Stretch still open (research-level, deferred)**: the existence/obstruction theorem for a *faithful* (non-trivial) self-model — can a proper part perfectly model the whole? — via **Lawvere's fixed-point theorem** and the diagonal argument. Mathlib carries only the powerset diagonal (`Function.cantor_surjective`/`cantor_injective`), not a general Lawvere theorem, so this must be built from scratch and is its own later session.

**Risk**: Core was LOW (clean extension of #9), as the roadmap predicted; the Lawvere/diagonal stretch remains high.

---

### Principle 11: Understandability

**Mobus**: "Systems can be understood (a corollary of #9) — Science."

**Current Lean state**: Implicit in the entire project (the project exists because systems can be understood).

**The "corollary" framing may be wrong.** Mobus labels this a corollary of Internal Models (#9), but that undersells what it's actually claiming. Having a model of a system (#9) is not the same as *understanding* a system. Understanding implies the model is *simpler* than the thing modeled — otherwise you've duplicated, not understood. This is a claim about the compressibility of nature, not just about the existence of models.

**Candidate formalizations**:

1. **Rosen's modeling relation** — Understanding = existence of a commuting square between a natural system and a formal system, with encoding/decoding morphisms. This is the classic mathematical biology approach. Rosen's *Life Itself* (1991) formalizes this; it may already exist in partial Lean form via the category theory community. **Research needed**: check Zotero for Rosen formalization attempts, check Mathlib for relational modeling structures.

2. **Kolmogorov complexity / compression** — Understanding = existence of a description of the system shorter than the system itself. A system is "understandable" iff its Kolmogorov complexity is less than its size. This is information-theoretic and connects to Complexity (#5). **Research needed**: Lean formalizations of Kolmogorov complexity exist in computability theory libraries.

3. **Category-theoretic abstraction** — Understanding = existence of a faithful functor from a simpler category to the system's shape category. The model preserves structure but has fewer objects/morphisms. This connects directly to the shape category infrastructure already built. **Research needed**: is "faithful functor from simpler source" a useful definition of "understanding"? What does "simpler" mean categorically?

4. **Epistemic framing** — Understanding is not a property of the system but of the *relationship between observer and system*. This would make #11 fundamentally different from #1-#10 (which are ontological). It would be a principle about the observer, not the observed. **Research needed**: Bunge's epistemology (Treatise Vols. 5-6), Klir's epistemological hierarchy of systems.

**Open question**: Is Understandability actually independent of #9? If so, the 12 principles contain a hidden epistemological axiom that Mobus's "corollary" framing obscures. This would be a genuine finding.

**Effort**: Depends on which formalization path. The categorical version (#3) could be attempted after Tier 1 as a test.
**Risk**: High but potentially high-reward — if #11 is independent, that's a contribution to the axiomatization.

---

### Principle 12: Improvability

**Mobus**: "Systems can be improved (a corollary of #6) — Engineering."

**Current Lean state**: Not formalized.

**The "corollary" framing may be wrong here too.** Evolution (#6) is blind — variation is random, selection is environmental. Engineering is *directed* — the designer has a model (#9), understands the system (#11), and intervenes to change its structure toward a goal. The difference is not incidental. Calling Improvability a corollary of Evolution is like calling architecture a corollary of erosion — both reshape structures, but one has intention.

**Candidate formalizations**:

1. **Accessible fitness improvements** — A system is improvable iff its configuration space contains accessible paths to higher-fitness configurations. This is a topological claim about fitness landscapes — that they are not all local maxima. **Research needed**: fitness landscape formalization (Kauffman, Stadler), accessibility in configuration spaces.

2. **Directed search with models** — Improvability = Evolution + Internal Models + a goal. The engineer holds a model of the system, a model of the desired state, and searches for interventions that move the system toward the goal. This makes #12 depend on #6 + #9 + an additional "goal" structure that none of the other principles provide. **Research needed**: Ashby's requisite variety as a constraint on improvability (the controller must be at least as complex as the controlled).

3. **Design as constrained optimization** — A system is improvable iff there exists a morphism from its current configuration to a better one that respects the system's structural constraints (boundaries, hierarchy, coherence). This connects to the 8-tuple constraints — improvement must preserve systemness. **Research needed**: constraint-preserving transformations in the existing Lean infrastructure.

4. **Agency framing** — Like #11's epistemic framing, #12 may be a principle about the *relationship between designer and system*, not about the system itself. Improvability requires an external agent with: (a) a model of the system (#9), (b) understanding of the system (#11), (c) a goal not supplied by the system's own dynamics, (d) the ability to intervene. This would make #12 depend on #11 (and transitively on #9), but add the new concept of *intentional intervention from outside the system boundary*.

**Open question**: Does Improvability add genuinely new structure (intentional external intervention) that neither Evolution nor any other principle captures? If so, it's not a corollary — it's the principle that distinguishes engineering from natural science, and its independence would be meaningful.

**Effort**: Depends on formalization path. The constraint-preserving transformation version (#3) could be attempted alongside Tier 1.
**Risk**: Medium-high. The philosophical depth is real but the formal versions are tractable if scoped carefully.

---

## Recommended Sequencing

### Tier 1: Structural (sets only, low risk, 2-3 months)

**Goal**: Formalize the three structural principles that form the foundation. Test the hypothesis that Complexity derives from the others.

1. **Complete Systemness (#1)** — `IsSystem` predicate, closure theorems, connect `RecursiveComponent` to `ConcreteSystem`
2. **Deepen Hierarchy (#2)** — `TimeScaleSeparation`, `NearDecomposable`, connect levels to subsystem category
3. **Formalize Complexity (#5)** — `StructuralComplexity` from 8-tuple, monotonicity theorem, test derivability from #1+#2+#3

**Axiomatization test after Tier 1**: Is Complexity independent? If it derives from Systemness + Hierarchy + Networks, the 12 principles reduce to 11 (or fewer).

### Tier 2: Cybernetic (sets → categories, medium risk, 3-6 months after Tier 1)

**Goal**: Formalize the principles that involve feedback, control, and representation. This is where categories become essential.

4. **Formalize Dynamics (#4)** — `DynamicalLaw`, composition of dynamics, multi-timescale decomposition
5. **Formalize Governance (#8)** — Governor-regulated decomposition, feedback loops, HCGS. Aligns with categorification roadmap Phase 4 (Joslyn).
6. **Formalize Internal Models (#9)** — Simulation relation, lens formalism (Myers). Depends on #4.
7. **Formalize Information (#7)** — Flow classification, knowledge state, channel constraints

**Axiomatization test after Tier 2**: Does Governance require Dynamics as a premise? Does Internal Models follow from Information + Dynamics? How many independent principles remain?

### Tier 3: Reflexive (categories from the start, high risk, future work)

**Goal**: Formalize the principles that involve self-reference and long-term change. These are research-level.

8. **Self-Models (#10)** — Lawvere fixed points, diagonal arguments
9. **Evolution (#6)** — Fitness, selection, accommodation. Temporal type theory or rewriting systems.
10. **Understandability (#11)** — Simplifying model existence. Corollary of #5 + #9.
11. **Improvability (#12)** — Directed evolution. Corollary of #6.

**Axiomatization test after Tier 3**: The ultimate deliverable — a dependency DAG of the 12 principles showing which arrows are provable theorems and which are independence witnesses. How many independent axioms does systems science actually need?

---

## Mathematical Foundation Strategy

Follow the existing progression established in the project:

| Tier | Foundation | Rationale |
|------|-----------|-----------|
| 1 | Sets/inductive types only | Structural principles are about what exists, not how things compose. Set theory is sufficient and lower-cost. |
| 2 | Sets first, categories when they reveal new theorems | Governance needs traced monoidal categories for feedback. Internal Models needs lenses. But start set-theoretic and upgrade when the categorical language makes a new theorem statable. |
| 3 | Categories from the start | Self-reference and evolution likely require higher-order structure that sets can't express cleanly. |

**The ct-sandbox role**: Use CatLab.jl for computational exploration of Tier 2-3 principles *before* attempting Lean formalization. Sketch → prototype in CatLab.jl → certify in Lean/Mathlib. This is the established workflow from the categorification roadmap.

**Do NOT start with categories for everything.** The categorification roadmap's design principle applies: "Don't categorify for its own sake. Each categorical upgrade must answer a question that the current formalization can't." Tier 1 principles do not need categories. Forcing them into categorical language would add infrastructure cost without conceptual gain.

---

## Initial Proof Scaffolding

### Systemness (#1): `Systems/Core/Systemness.lean`

```lean
-- The systemness predicate: closure under decomposition and composition
structure SystemClosure (α : Type*) [ActsOn α] where
  -- Every component of a system is either atomic or itself a system
  component_systemness : ∀ (σ : ConcreteSystem α) (c : α),
    c ∈ σ.composition → IsAtomic c ∨ ∃ σ', c = σ'.thing ∧ σ' ≤ σ
  -- Interacting systems compose into a system
  composition_closure : ∀ (σ₁ σ₂ : ConcreteSystem α),
    Interacting σ₁ σ₂ → ∃ σ, σ₁ ≤ σ ∧ σ₂ ≤ σ
```

### Hierarchy (#2): extend `Systems/Core/Level.lean`

```lean
-- Time-scale separation: lower levels are faster
structure TimeScaleSeparation {α : Type*} [Preorder α]
    (ls : LevelStructure α) (T : Type*) [LinearOrder T] where
  timescale : (L : Set α) → L ∈ ls.levels → T
  separation : ∀ (i j : Fin ls.levels.length),
    i < j → timescale (ls.levels[i]) ‹_› < timescale (ls.levels[j]) ‹_›

-- Simon near-decomposability
structure NearDecomposable {α : Type*} [ActsOn α]
    (σ : ConcreteSystem α) (modules : List (Set α)) where
  covers : ∀ c ∈ σ.composition, ∃ m ∈ modules, c ∈ m
  within_stronger : ∀ m ∈ modules, ∀ x y ∈ m,
    interactionStrength x y > betweenModuleThreshold
  between_weaker : ∀ m₁ m₂ ∈ modules, m₁ ≠ m₂ → ∀ x ∈ m₁, ∀ y ∈ m₂,
    interactionStrength x y < betweenModuleThreshold
```

### Complexity (#5): `Systems/Mobus/Complexity.lean`

```lean
-- Structural complexity measures from the 8-tuple
structure StructuralComplexity
    (sys : MobusSystem α κ μ π τ η δ) where
  -- Number of components
  componentCount : ℕ := sys.components.toFinset.card
  -- Hierarchical depth (requires LevelStructure on components)
  depth : ℕ
  -- Network density: edges / (n * (n-1)) for directed graph
  density : ℚ
  -- Component-kind diversity (number of distinct types)
  kindCount : ℕ

-- Monotonicity: adding subsystems doesn't decrease complexity
theorem complexity_monotone_composition
    (σ₁ σ₂ : MobusSystem ...) (h : σ₁ ≤ σ₂) :
    (StructuralComplexity σ₁).componentCount ≤
    (StructuralComplexity σ₂).componentCount
```

These are scaffolds, not implementations. The actual Lean code will need to resolve type-parameter threading and Mathlib API details. The scaffolds establish what theorems we're aiming for.

---

## The Axiomatization Question

After each tier, we can begin testing dependency hypotheses:

| Hypothesis | Test after | Expected result |
|-----------|-----------|-----------------|
| Complexity derives from Systemness + Hierarchy + Networks | Tier 1 | Likely provable for structural complexity; information-theoretic complexity may be independent |
| Governance requires Dynamics as premise | Tier 2 | Likely yes — feedback requires temporal evolution |
| Internal Models derive from Information + Dynamics | Tier 2 | Partially — the existence of models may be independent, but their operation requires #4 and #7 |
| Understandability is a corollary of Internal Models | Tier 3 | **Uncertain** — Mobus says yes, but the compression/simplification requirement may be independent. If #11 adds an epistemic axiom (models must be simpler than modeled), it's not a corollary. |
| Improvability is a corollary of Evolution | Tier 3 | **Uncertain** — Mobus says yes, but directed intervention (goal + model + agency) may add structure that blind evolution lacks. If #12 adds intentional external intervention, it's independent. |
| Evolution is independent of all other principles | Tier 3 | Likely yes — it adds selection/variation structure |
| #11 and #12 are epistemological/agential, not ontological | Cross-tier | **Open question** — if true, the 12 principles split into two kinds: 10 about what systems ARE/DO, and 2 about what OBSERVERS/DESIGNERS can do WITH systems. This would be a structural insight about the principles themselves. |

The ultimate deliverable: a dependency DAG showing which principles are axioms (independent) and which are theorems (derived). This is what turns the 12 principles from a list into a theory.

**The 11/12 question is potentially the most interesting finding.** If Understandability and Improvability are *not* corollaries but independent principles about the observer-system and designer-system relationships, then Mobus's framework contains a hidden epistemological/agential layer that the "corollary" labeling obscures. Demonstrating this formally would be a contribution to the theory, not just to the formalization.
