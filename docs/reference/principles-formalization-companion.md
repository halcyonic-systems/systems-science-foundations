# Principles Formalization — Plain English Companion

*What each formalization says, what it means, and what's left*

**Last updated**: 2026-05-24
**Lean source**: `Systems/Core/Systemness.lean`, `Systems/Core/Level.lean`, `Systems/Core/Complexity.lean`, `Systems/Core/Dynamics.lean`
**Technical roadmap**: `principles-formalization-roadmap.md`

> **Update discipline**: The axiom table below is the PRIMARY output of every formalization session. After `lake build` succeeds on new theorems, update this table FIRST — one plain English sentence per result, no Lean type names. Then update the per-principle sections, tasknote, roadmap, and session file. If the axiom can't be stated in one sentence, the formalization isn't understood yet.

---

## What we're doing

Mobus lists 12 principles of systems science. We're formalizing them in Lean 4 — turning each principle into precise definitions and machine-checked theorems. The goal isn't to verify what systems theorists already know. It's to discover what the principles actually say when you force them to be precise: which are independent axioms, which are theorems derivable from others, and whether the 12 reduce to a smaller set.

---

## Principle 1: Systemness

**Mobus's claim**: "Bounded networks of relations among parts constitute a holistic unit. Systems interact with other systems, forming yet larger systems. The Universe is composed of systems of systems."

### What we formalized

**RecursiveSystem** — A system is a tree where each internal node is a genuine system (with components, environment, bonds, and coherence constraints) and each leaf is a process primitive (an atomic work process that doesn't decompose further). This is Mobus's recursive decomposition equation enriched with Bunge's system semantics at every level.

**WellFormed** — At every level of decomposition, the children correspond exactly to that level's component set. No phantom components (listed in the system but not represented by any child), no orphans (children that don't belong to the composition).

**IsOrganized / IsAggregate** — A set of things is organized if at least two of its members interact (are bonded). An aggregate is the same components with no bonds — a pile, not a system. Every system is organized by definition; assembly (already formalized) is the transition from aggregate to organized.

### What we proved

1. **Decomposition terminates** — you can't decompose forever; every path hits a process primitive.
2. **Closure under decomposition** — if the whole is well-formed, every subsystem you encounter is well-formed too. This is the formal content of "every component is either atomic or itself a system."
3. **Every level is organized** — no mere aggregate hides inside a genuine system.
4. **Closure under composition** — two systems with disjoint compositions and at least one cross-boundary bond compose into a valid supersystem. The composed system's environment is (E₁ ∪ E₂) \ (C₁ ∪ C₂) — the unique minimal environment satisfying `structure_on`.

### The one-line axiom

> *A system is a bounded, organized collection of things, each of which is either a process primitive or itself a system.*

### What we found

The existing Lean code had an inductive tree type (`RecursiveComponent`) that captured "things have parts that have parts" — but said nothing about whether those parts form genuine systems. It was a tree shape without system semantics. The formalization forced us to notice this gap and close it.

**Composition closure is unconditional at the type level.** Neither the disjointness hypothesis nor the interaction hypothesis is needed for the CES coherence proofs. The union-of-compositions, difference-of-environments, union-of-structures construction produces a valid ConcreteSystem for ANY two systems. The hypotheses add physical content — disjointness ensures distinct systems, interaction ensures meaningful composition — but the mathematical construction doesn't require them. This means the space of systems is closed under arbitrary union, not just interaction-mediated composition.

**The environment formula must be union, not intersection.** Intersection breaks `structure_on`: if σ₁ has a structure relation referencing an environmental thing unknown to σ₂, the intersection drops it, but the structure relation still points there. The union formula is the unique minimal environment that keeps all structure relations valid.

### Design notes

- We use Bunge's CES triple (composition, environment, structure) at each level, not Mobus's full 8-tuple. Systemness is about what makes something a system vs. an aggregate — bonds, composition, environment. The 8-tuple adds operational content (flow networks, transforms, time scales) that belongs to later principles.
- The `thing : α` identifier on each node assumes crisp, well-bounded systems. For fuzzy systems (Mobus §2.2), where the boundary is an analytical choice rather than an ontological fact, this assumption strains. A future formalization could weaken it.
- We do NOT assume the universe is a closed system. The top-level node's identifier is structurally orphaned — no parent references it — but we don't assert closure.

---

## Principle 2: Hierarchy

**Mobus's claim**: "Systems are processes organized in structural and functional hierarchies... The next higher layer consists of subsystems composed of components from the lower layer in which component interactions within the subsystem are stronger than interactions between components in other subsystems."

### What we formalized

**TimeScaleSeparation** — Each level in a hierarchy has a characteristic time scale, and lower levels are strictly faster. Formalized as a strictly monotone map from level indices to an ordered time-scale type.

**InteractionStrength** — A quantitative measure of how strongly one thing acts on another. Generalizes the existing binary relation (acts-on-or-doesn't) to a graded notion. Parameterized abstractly — concrete instances might use flow capacity, coupling coefficients, or information transfer rates.

**NearDecomposable** — A system is nearly decomposable (Simon 1962) when its components partition into modules where:
- Every within-module interaction exceeds a threshold
- Every between-module interaction falls below that threshold

This is what distinguishes genuine hierarchy from arbitrary nesting.

### What we proved

1. **Timescale injectivity** — no two levels share a time scale. Each level operates at a distinct tempo.
2. **Within exceeds between** — in a near-decomposable system, pick any two components in the same module and any component in a different module. The within-module pair always interacts more strongly than the cross-module pair. This is what Simon says informally; we proved it.
3. **Conditional time-scale separation** (Simon's implication) — IF interaction strength monotonically determines time scale (`StrictAnti f`), THEN within-module dynamics are strictly faster than between-module dynamics. One-line proof applying `StrictAnti` to `within_exceeds_between`.

### The one-line axioms

> *A hierarchy is a level structure where lower levels are strictly faster.* (TimeScaleSeparation)

> *A system is hierarchical when its components cluster into modules where within-module interaction uniformly exceeds between-module interaction.* (NearDecomposable)

### What we found

These are two separate claims with a conjectured relationship: near-decomposability is the STRUCTURAL CAUSE (strong internal coupling → fast internal dynamics), time-scale separation is the OBSERVABLE CONSEQUENCE (each level runs at a distinct tempo). Simon states this informally. The formal connection requires one additional assumption — that interaction strength determines dynamical speed — which is exactly what Dynamics (Principle 4) should provide.

**Simon's implicit assumption is `StrictAnti f`: stronger interaction → shorter time scale.** The conditional theorem isolates this precisely. The proof is one line — the mathematical content is in the STATEMENT, not the proof. Naming the assumption IS the contribution. The full unconditional version awaits Dynamics (#4), which would provide the concrete `f`. The conditional version identifies EXACTLY what additional assumption converts structural hierarchy into temporal hierarchy.

---

## Principle 3: Networks — already complete

Fully formalized in `FlowNetwork.lean`, `Bond.lean`, `Interface.lean`. Directed graphs with capacity labels, source/sink classification, bipartite flow constraints. No further work needed at Tier 1.

---

## Principle 4: Dynamics — complete (structural)

Dynamics.lean (482 lines) formalizes everything Mobus means by "systems are dynamic on multiple time scales" at the structural level. The file grew from bridge infrastructure (connecting to Simon's conditional and Simonian complexity) into a full axiomatization across W21.

**What we proved:**

1. **Dynamics compose as products.** `DynamicSystem.compose` gives the composed state space S₁ × S₂ with independent evolution. Both projection theorems proved (`rfl`): the composed dynamics preserves each subsystem's state evolution.

2. **Coupled dynamics generalizes independent.** `CoupledDynamicSystem` captures mutual influence (each law depends on both states). `DynamicSystem.toCoupled` embeds independent dynamics as the special case where each law ignores the other subsystem.

3. **Equilibrium theory is complete.** `IsEquilibrium` (fixed point), `product_equilibrium` (products of equilibria are equilibria), `coupled_equilibrium_iff_fixed` (biconditional — coupled equilibrium ↔ fixed point of combined law), `independent_equilibrium_is_coupled` (independent equilibria are coupled equilibria), `equilibrium_iterate` (equilibria are preserved under iteration — trajectory from equilibrium is constant).

4. **Flows compose.** `Flow` (semigroup action on state space, `AddMonoid T`) with `flow_zero` and `flow_add` axioms. `Flow.compose` gives product flows with both projections proved.

5. **Timescale decomposition is structural.** `TimescaleDecomposition` separates fast (within-module, frozen at equilibrium) from slow (full coupling). Five theorems: fast₁ and fast₂ have the reference equilibrium as a fixed point, slow dynamics is stationary at the reference, and for independent dynamics the fast laws recover the original subsystem laws exactly.

6. **Simon's bridge is complete.** `InteractionDynamicsBridge` names the physical assumption (StrictAnti: stronger interaction → shorter time scale). `NearDecomposable.simon_from_bridge` composes this with the conditional from Level.lean to give full time-scale separation.

**What we found:**

- The dynamics hierarchy is a hierarchy of fixed-point approximations (Finding 9). Independent → coupled → multi-timescale is zeroth-order → exact → approximate. Near-decomposability is the condition that makes zeroth order a good approximation.
- Governance is independent of dynamics (Finding 10). The set point is genuinely new structure — `GovernanceSubsystem.toCoupled` shows exactly what governance adds beyond coupling.

**What's deferred:** Quantitative convergence (metric on state space), stochastic transitions (measure theory), input-dependent evolution (open systems). These are research-level extensions, not gaps in the axiomatization.

---

## Principle 8: Governance — Lens Bridge

Governance.lean captures Mobus's HCGS: Homeostat, GovernanceSubsystem, TwoLevelGovernance. The Lens Bridge (Lens.lean, 2026-05-25) adds the categorical cybernetics connection.

**What we proved:**

1. **Lenses form a category.** `Lens.compose_assoc`, `Lens.id_compose`, `Lens.compose_id` — symmetric lenses compose associatively with identity. This gives hierarchical governance composition at arbitrary depth.

2. **A homeostat IS a lens + reference value.** `Homeostat.toLens` maps sensor → get, (error ∘ correct) → put. The set point is baked into the backward channel. `Homeostat.feedbackLaw_eq_lens` proves the feedback law decomposes as get-then-put (observe, then correct) — `rfl`.

3. **Homeostats compose via lenses.** `Homeostat.composeLens` composes two homeostats through their lens structure. This is what `TwoLevelGovernance` does manually; lens composition does it structurally.

4. **TwoLevelGovernance parameterizes the lens.** `TwoLevelGovernance.opsLens_eq` shows the operations homeostat's lens at a fixed coordination state. The coordinator decides *which* lens is active by modifying the set point — this is the additional governance structure that lenses alone don't capture.

**What we found:**

- The Conant-Ashby theorem's structural skeleton is the walking arrow. `ConantAshbySkeleton` defines a regulator with a model homomorphism `model : R → S` such that `observe ∘ model = regView` (the commuting diagram). This is the same structure as K ≅ **2**: a system is a morphism, and a good regulator is a morphism. The irreducible categorical content of "being a system" and "governing a system" is **2**.

- Three modern frameworks (Capucci et al. categorical cybernetics, Spivak-Niu polynomial functors, Myers CST) all identify the lens as the primitive. Our formalization appears to be the first to connect Mobus's HCGS to this literature in a proof assistant.

- Asymmetric lens composition (where forward and backward types differ) requires profunctor optics — a future extension if needed. For governance, symmetric lenses suffice because the observation and correction share a type.

---

## What the axioms look like (emerging)

As the formalizations accumulate, each principle is converging toward a one-line axiom:

| # | Principle | Axiom (candidate) |
|---|-----------|-------------------|
| 1 | Systemness (identity) | A system is a bounded, organized collection, each component of which is primitive or itself a system |
| 1 | Systemness (closure) | Any two systems compose into a supersystem — unconditional at both CES and 8-tuple levels |
| 2 | Hierarchy (structure) | A system is hierarchical when within-module interaction uniformly exceeds between-module interaction |
| 2 | Hierarchy (dynamics) | In a hierarchy, lower levels are strictly faster |
| 3 | Networks | A system's internal structure is a directed flow network with capacity constraints |
| 4 | Dynamics (state) | A system has a state space and a law governing how state evolves |
| 4 | Dynamics (composition) | When systems compose, their state spaces multiply and their dynamics combine independently |
| 4 | Dynamics (coupling) | Coupled dynamics generalizes independent: each subsystem's evolution depends on the other's state |
| 4 | Dynamics (equilibrium) | Equilibria compose as products; coupled equilibria are fixed points of the combined law; independent equilibria are coupled equilibria |
| 4 | Dynamics (flow) | A flow is a semigroup action on state space — deterministic evolution parameterized by time, composable as products |
| 4 | Dynamics (timescale) | Coupled dynamics decomposes into fast (freeze other subsystem, evolve independently) and slow (full coupling) around any equilibrium |
| 4 | Dynamics (bridge) | Stronger interaction produces faster dynamics — this is what converts structural hierarchy into temporal hierarchy |
| 5 | Complexity | **Not an axiom.** Structural measures derive from #1+#2+#3. Simonian state-space reduction bridges #1+#2 to #4. Behavioral complexity is Mobus's own open problem. |
| 8 | Governance (homeostat) | A governed process has a reference state (set point), a sensor, an error function, and a corrective action — the feedback loop |
| 8 | Governance (asymmetry) | Governance is coupled dynamics plus a reference state — the set point is genuinely new structure not in Dynamics #4 |
| 8 | Governance (hierarchy) | Higher governance levels modify lower levels' set points — feed-downward maps to TimescaleDecomposition with goals at each level |
| 8 | Governance (lens) | A homeostat IS a bidirectional lens (observe/correct) equipped with a reference value — the set point parameterizes the backward channel |
| 8 | Governance (Conant-Ashby) | A good regulator contains a homomorphic model of the system it regulates — the walking arrow connects governance to K ≅ **2** |
| 9 | Internal Models | **Theorem, not an axiom.** A subsystem that holds a model of another system and simulates it one step ahead necessarily predicts it at every future step — one-step correctness lifts to all horizons. Anticipation is structural, not an extra feature. The model map is exactly the homomorphism a good regulator needs (#9 supplies #8). |

The axiomatization question: how many of the 12 are independent? If Complexity derives from the structural principles, we're already down to fewer than 12. The ultimate deliverable is a dependency DAG showing which principles are axioms and which are theorems.

---

## Findings the prose tradition doesn't contain

The formalization is systematically producing results that are stronger than, differently structured from, or absent in the existing literature — including Bunge's set-theoretic definitions, Mobus's informal principles, and Simon's verbal arguments. These are not corrections — they are discoveries that only become visible under machine-checked proof.

1. **Composition closure is unconditional.** Mobus says "systems interact with other systems, forming yet larger systems." The formalization says the interaction isn't even required — the CES construction produces a valid system from ANY two systems. The disjointness and interaction hypotheses add physical meaning but are mathematically unnecessary. The space of systems is closed under arbitrary union, not just interaction-mediated composition. This is stronger than the principle claims.

    *What this means practically:* At Bunge's CES level, the boundary of what counts as "a system" is the modeler's choice — composition can't fail. But this permissiveness has limits: at Mobus's 8-tuple level, composition must respect flow constraints, boundary completeness (B = ⟨P, I⟩), and interface bipartiteness. The constraints that make composition non-trivial come from Mobus's extensions (flows, boundaries), not from Bunge's foundation (CES). Composition is free at the foundation; the 8-tuple is where the boundary constrains you. A composed system of non-interacting parts is valid at the CES level but boring — an aggregate of systems. The cross-boundary bonds are what create emergent structure. For BERT: composition at the structural level should be unconstrained; flow and boundary validation is a separate, later check.

2. **Simon's bridge has a named gap.** Simon's 1962 argument jumps from *how tightly coupled* components are (structural) to *how fast* things change (temporal). That jump requires an unstated assumption: coupling strength determines dynamical speed. This is usually true — tightly coupled springs oscillate faster, strongly connected neurons synchronize quicker, closely linked markets equilibrate sooner. But it is not a logical necessity. Tectonic plates are tightly coupled and move slowly. The formalization isolates the assumption precisely: a strictly anti-monotone map from interaction strength to time scale. It proves: IF this map exists, Simon's conclusion follows. If it doesn't, the argument breaks. Hierarchy is really two independent claims glued by this assumption, and Dynamics (#4) is what provides it. For 60 years, systems theorists have used Simon's argument as if the structural and temporal claims are the same thing. They are not.

    *What this means practically:* It tells you *when* Simon's argument applies (domains where coupling → speed, like springs, circuits, markets) and *when* it doesn't (domains where coupling and speed are independent, like geology, certain institutional systems). When building hierarchical models, the question is not just "are these modules tightly coupled?" but "does tighter coupling actually produce faster dynamics in this domain?"

3. **The environment formula is forced.** When composing two systems, the supersystem's environment must be (E₁ ∪ E₂) \ (C₁ ∪ C₂). This isn't a design choice — intersection provably breaks the `structure_on` coherence constraint. The union formula is the unique minimal environment that keeps all structure relations valid. This kind of uniqueness result doesn't exist in the prose tradition, where environment is defined informally.

4. **Complexity decomposes into other principles — under Mobus's own scoping.** Mobus (Ch. 4) distinguishes structural complexity from Simonian complexity (state-space explosion tamed by near-decomposability) and explicitly defers behavioral complexity as future research. The formalization shows each piece is accounted for: structural complexity derives from #1+#2+#3 (proved in Complexity.lean with only Core imports). Simonian complexity is a bridge theorem connecting Hierarchy (#2) to Dynamics (#4) — structurally parallel to Simon's conditional, it names what Dynamics provides without requiring a new axiom. Behavioral complexity is Mobus's own open problem, not part of the stated principle. No part of Complexity as Mobus scopes it requires new axioms. The 12 reduce by at least 1.

5. **Diversity derives from ActsOn, not from a new typing system.** The session plan flagged component-kind diversity as the potential independence locus. The formalization resolves this: two components are "of the same kind" iff they have identical interaction profiles (SameKind equivalence). This is definable from ActsOn alone — the equivalence relation, its reflexivity/symmetry/transitivity, and the well-definedness of equivalence classes all derive from Systemness. No new type parameter or classification system needed.

    *What this means practically:* BERT and GSR could infer component types from interaction patterns rather than requiring manual labels. Two components that interact with the same things in the same ways ARE the same kind — no taxonomy needed.

6. **Complexity lives in Core, not Mobus.** The session plan pre-resolved file placement as `Systems/Mobus/Complexity.lean` (complexity uses 8-tuple data). The formalization proves this wrong: the CES triple suffices. The file is `Systems/Core/Complexity.lean`. The placement IS the derivability argument — if it compiles with only Core imports, complexity doesn't need the 8-tuple.

7. **8-tuple composition is also unconditional.** We predicted that Mobus's boundary constraints (bipartite external flows, boundary completeness, interface containment) might make composition conditional — that the boundary would be the point where "modeler's choice" ends. The formalization proves otherwise: MobusSystem.compose compiles with the same hypotheses as CES-level compose (disjoint components only). The bipartite property transfers because composition only REMOVES external edges (reclassifying them as internal when both endpoints become components), never adds them. The remaining edges still cross between environment and interfaces. Mobus's boundary is an organizational tool, not a composition gate.

    *What this means practically:* The entire Mobus 8-tuple — flow networks, boundaries, interfaces, capacity labels — imposes no composition constraint beyond what the minimal CES triple requires. BERT model composition at the full 8-tuple level is as free as at the structural level. Validate flow structure AFTER composing, not as a precondition.

8. **Unconditional composition is structurally inevitable, not accidental.** The reason composition works at both CES and 8-tuple levels goes deeper than "the proofs happen to go through." All constraints in both formalisms are either UNIVERSAL (for all edges/components, P) or EXISTENTIAL-ABOUT-INTERNALS (there exist bonded pairs in the composition). Universal constraints are preserved when edges are removed. Internal existential constraints are preserved because composition doesn't modify internal structure. Composition only removes external edges (reclassifies as internal) and never adds edges. So ANY constraint of these two forms is composition-safe. This is a design property of Bunge's and Mobus's formalisms — and neither of them knew it.

    *What this means practically:* Any future extension to the 8-tuple that uses universal or internal-existential constraints will also compose unconditionally. Composition safety is a structural invariant of the formalism, not something that needs to be re-verified for each new constraint.

9. **The dynamics hierarchy is a hierarchy of fixed-point approximations.** The coupled equilibrium theorem (`coupled_equilibrium_iff_fixed`) reveals that coupled equilibrium is not a new concept — it's just equilibrium of the combined law on the product state space. The coupling doesn't create new kinds of stability; it changes which function you're finding fixed points of. This means the entire dynamics hierarchy — independent → coupled → multi-timescale — is a hierarchy of fixed-point approximations: product equilibria are zeroth order, coupled equilibria are exact, and near-decomposability is the condition that makes zeroth order a good approximation. Multi-timescale decomposition, when formalized, will be: coupled fixed points are "close to" product fixed points when coupling is weak.

    *What this means practically:* This gives multi-timescale decomposition a clean formal target: a metric on equilibria parameterized by coupling strength, with near-decomposability as the bound. For BERT, it means model quality can be measured by how close the coupled equilibrium is to the product equilibrium — a computable proxy for "how well-decomposed is this model?"

10. **Governance is independent — the set point is the new primitive.** CoupledDynamicSystem captures mutual influence between subsystems. GovernanceSubsystem extends it with a reference state (set point), error function, and asymmetric feed-downward. The `toCoupled` forgetful map shows the exact structure governance adds: when you forget the set point and error function, you recover plain coupled dynamics. The forgetting IS the proof that governance adds something dynamics doesn't have. Goal-directed regulation — the feedback loop with a reference state — is genuinely new structure.

    *What this means practically:* When modeling in BERT, a governance subsystem is not just "two things that influence each other." It's a regulator with an intended state. BERT should distinguish governed processes (with set points) from merely coupled ones. The set point is user-specifiable — it's what the modeler says the system is TRYING to maintain.

11. **Governance and systems share a categorical root — the walking arrow.** The Conant-Ashby theorem (1970) says a good regulator must contain a homomorphic model of the system it regulates. The formalization reveals this is the walking arrow: a morphism R → S making an observation diagram commute. K ≅ **2** says a system IS a morphism (relations depend on things). Conant-Ashby says governance IS a morphism (the regulator models the system). The irreducible categorical content of "being a system" and "governing a system" is the same structure: **2**. The `Homeostat.toLens` decomposition makes this concrete — the feedback law is get-then-put, the bidirectional channel of a lens. Three independent modern frameworks (Capucci et al. categorical cybernetics, Spivak-Niu polynomial functors, Myers CST) all converge on this same primitive. Our formalization appears to be the first to connect Mobus's HCGS to categorical cybernetics in a proof assistant.

    *What this means practically:* The lens decomposition tells you that every governance structure has exactly two channels: a forward observation channel and a backward correction channel, parameterized by a reference value. For BERT, this means governance subsystems should be modeled as bidirectional connections with an explicit set point, not as generic coupled processes. The Conant-Ashby connection means the regulator's "model" of the system is formally the same structure as the system itself — the walking arrow at every level.

12. **Anticipation is structural, not an advanced feature — and Internal Models needs no new axiom.** Mobus lists internal models as a principle and notes they range "up to complex anticipatory models," which reads as: anticipation is a sophisticated capability some models have. The formalization shows anticipation is *automatic*. Any internal model whose dynamics simulate the system for ONE step (the commuting square `model ∘ internalDyn = systemDyn ∘ model`) necessarily predicts it for ALL steps (`InternalModel.tracks`, proved by induction on the horizon). There is no separate "anticipatory" axiom — a correct one-step model is already a correct n-step predictor. Moreover, Internal Models is a **theorem-tier** principle: the model map is just a dynamics homomorphism (`Function.Semiconj`), built entirely from Dynamics (#4) with no new primitive — so realizing #9 adds no axiom (a second reduction after Complexity). And the model map is *exactly* the homomorphism a good regulator must contain: `InternalModel.toConantAshby` shows every internal model induces the Conant-Ashby skeleton, so #9 supplies precisely the structure #8 requires. Modelling a system and governing a system are the same walking arrow.

    *What this means practically:* For BERT/GSR, model fidelity is a **one-step property to check** — if a subsystem correctly tracks another for a single step, it is automatically a valid predictor at any horizon; you don't separately validate "anticipation." And a governed process's internal model and the regulator's required model are the same object, so governance and prediction reuse one structure.

13. **The Conant-Ashby Good Regulator theorem's engine is the strict concavity of −x·log x — now machine-checked.** Conant & Ashby (1970) prove the *information-theoretic* result that the simplest *optimal* (entropy-minimizing) regulator is a deterministic mapping `h: S→R` — a model of the system. The entire force of their proof is one entropy fact: shifting outcome probability mass to make `p(Z)` more unequal strictly lowers `H(Z)`. Formalized (`GoodRegulator.lean`, `negMulLog_transfer`), that fact is exactly the strict (Schur-)concavity of `negMulLog`: a fixed-sum transfer toward greater imbalance strictly decreases `negMulLog a + negMulLog b`. This is the genuine theorem's core, and reading the 1970 paper directly was decisive — it showed the earlier `ConantAshbySkeleton` (and the `InternalModel` simulation result) are the *structural/representational* direction (R→S), whereas the theorem's actual mapping is the dual *determination* direction `h: S→R`, forced by entropy. The determinism wrapper (an optimal regulator can't spread one state's mass over two outcomes without lowering entropy → it must be a mapping) is scoped with a full proof strategy in the file; the hard, novel part — the entropy engine — is verified.

    *What this means practically:* "A good regulator is a model of the system" is not a metaphor or a structural convenience — it is *forced by entropy minimization*, and the forcing mechanism is a one-line concavity fact now in the library. This grounds the K ≅ **2** "governing = modelling" claim in the original information-theoretic theorem, not only the walking-arrow skeleton.

These findings share a pattern: formalization reveals structure that informal reasoning cannot access. Each finding has both a theoretical and a practical consequence — the theoretical result changes how we understand the principle; the practical consequence informs how BERT, GSR, and Halcyonic modeling workflows should behave. The Lean proofs force the discoveries; the plain-English implications are the deliverable.

---

## Simon's argument, formalized

Simon's "Architecture of Complexity" (1962) is the most cited structural argument in systems science: near-decomposable systems exhibit time-scale separation because strong within-module coupling produces fast internal equilibration, leaving only slow between-module dynamics. Mobus, Bunge, and Klir all reference it. None formalized it.

We built the argument as a chain: **NearDecomposable** (structural partition) → **StrictAnti bridge** (Simon's unstated assumption: stronger interaction → faster dynamics) → **CoupledDynamicSystem** (mutual-influence evolution) → **TimescaleDecomposition** (fast/slow split around equilibrium) → **fast equilibria = product equilibria** (what fast dynamics converges to).

The chain identifies what each principle contributes: Systemness gives composition, Hierarchy gives modules, Dynamics gives the bridge. No single principle produces multi-timescale behavior alone. The formalization also isolates Simon's unnamed assumption, reveals the decomposition is universal (near-decomposability justifies it, doesn't define it), and shows the dynamics hierarchy is fixed-point approximations on product state space.

Full treatment: `docs/reference/simon-argument-formalized.md`

---

## Program status

Seven of twelve principles resolved (~6,330 lines, zero `sorry`):

| # | Principle | Tier | Verdict | Key result |
|---|-----------|------|---------|------------|
| 1 | Systemness | 1 | **Axiom** | Composition closure unconditional at CES and 8-tuple |
| 2 | Hierarchy | 1 | **Axiom** | Simon's implicit assumption named |
| 3 | Networks | 1 | **Axiom** | Complete prior to this program |
| 4 | Dynamics | 2 | **Axiom** (complete, structural) | DynamicSystem, coupled, equilibrium, Flow, timescale decomposition, Simon's bridge |
| 5 | Complexity | 1 | **Theorem** | Derives from #1+#2+#3. First reduction: 12 → ≤11 |
| 8 | Governance | 2 | **Axiom** + lens bridge | Set point is new structure; Homeostat = lens + setPoint; Conant-Ashby skeleton connects to K ≅ **2** |
| 9 | Internal Models | 2 | **Theorem** | Simulation relation lifts to all horizons (anticipation is structural); model map = Conant-Ashby homomorphism, so #9 supplies #8. No new axiom — second reduction. |

**Next**: Principle 10 (Self-Models) is now unblocked — it's the S = R case of #9, needing fixed-point machinery (Lawvere). Principle 7 (Information) is also open (channel capacity on flow networks, depends #3, done). Remaining unresolved: #6 Evolution, #7 Information, #10 Self-Models, #11 Understandability, #12 Improvability.
