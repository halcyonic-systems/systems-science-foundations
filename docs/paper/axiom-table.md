# Mobus's 12 Principles of Systems Science — 8 Axioms + 4 Theorems

> **Recount 2026-09-04** (independence matrix + environment build, `docs/paper/p3-reading-edition.md` §9): the eight are not eight independents. Four ontological primitives (#1, #4, #6 as `EvolutionE`, #8 as `HomeostatD`), two structural refinements of #1 (#3, #2), two agential stances (#11, #12). #8's independence from #6 holds provided evolution's criterion is external, which is Mobus's own clause. The list below is kept as the pre-recount reference.

*One line each, grouped by verdict. Every entry is machine-checked in Lean 4 (`systems-science-foundations`, zero `sorry`). This is the clean reference list / paper Fig. 2. Full discussion: `../reference/principles-formalization-companion.md`; dependency graph: `dependency-dag.mmd`.*

## Axioms (8 — independent)

**Ontological — hold for any system:**
1. **Systemness** — A system is a bounded, organized collection of systems/primitives; any two systems compose into a supersystem.
2. **Hierarchy** — Organization is hierarchical: within-module interaction exceeds between-module, and lower levels run faster. *(2026-09-04: showcase moved from Bunge's `ImmediateAncestor` to Mobus Eq. 4.3 `Hierarchical` in `Principles/Hierarchy.lean`; presupposes #1 by construction.)*
3. **Networks** — A system's interior is a directed flow network with capacities.
4. **Dynamics** — A system has a state space and an evolution law; composition multiplies state spaces and combines laws.
8. **Governance** — A governed system has a set-point (reference) not contained in its dynamics; a good regulator contains a homomorphic model of what it regulates (K ≅ **2**).

**Blind change — a near-universal axis:**
6. **Evolution** — A system changes under blind, fitness-non-decreasing environmental selection; needs no model, goal, or understanding.

**Agential — about the observer/designer relation, not the system's complexity:**
11. **Understandability** — To understand a system is to hold a model strictly *simpler* than it (an onto, lossy, non-degenerate compression). *Observe / GET.*
12. **Improvability** — To improve a system is for an agent with a model + an external goal to intervene on its dynamics from outside. *Intervene / PUT.*

## Theorems (4 — derived, not axioms)

5. **Complexity** — Every structural complexity measure is a function of #1 + #2 (+ #3's data, which is #1's `structure'` field; import audit 2026-09-03) (the first reduction: 12 → ≤ 11).
9. **Internal Models** — A one-step-correct internal model is correct at *every* horizon (anticipation is automatic); a Rosen fast model gaining `lead` steps per tick runs `n·lead` ahead, with lockstep the `lead = 1` case; the model map is exactly the good-regulator homomorphism, so #9 supplies #8.
10. **Self-Models** — A self-model is the diagonal case of #9; existence is trivial (the identity), so the content is faithfulness, not existence — and faithfulness is expensive: an accurate *fast* self-model (lead ≥ 2) forces its own orbit into periodicity (perfect self-anticipation collapses time).
7. **Information** — Information is a difference that makes a difference (Bateson); Shannon entropy is a bounded special case (entropy ≤ Hartley nonspecificity, equality at the uniform distribution).

## Foundational profile (machine-checked)

*Kernel-computed via `#print axioms` on one showcase theorem per principle (`scripts/axiom-profile.sh`). `constructive` = no axioms; `choice-free` = `propext`/`Quot.sound` only; `classical` = pulls in `Classical.choice`. This is the rigorous analogue of a "proof vector" (cf. arXiv:2504.00063) — dependencies are computed, not asserted. Note: SSF's 8 systems axioms are structures/defs, not Lean `axiom`s, so the systems-level dependency vector lives in `dependency-dag.mmd`, not here; this column is a foundational-purity signal.*

| # | Principle | Headline theorem | Foundational profile |
|---|-----------|------------------|----------------------|
| 1 | Systemness | `ConcreteSystem.composition_organized` | constructive |
| 2 | Hierarchy | `ancestor_trans` | constructive |
| 3 | Networks | `FlowNetwork.toRelation_irrefl` | constructive |
| 4 | Dynamics | `coupled_equilibrium_iff_fixed` | choice-free |
| 5 | Complexity | `sameKind_equivalence` | constructive |
| 6 | Evolution | `evolvable_but_not_improvable` | classical |
| 7 | Information | `entropy_le_log_card` | classical |
| 8 | Governance | `Homeostat.target_is_equilibrium` | constructive |
| 9 | Internal Models | `AnticipatoryModel.tracks` | choice-free |
| 10 | Self-Models | `FastSelfModel.accurate_forces_periodic` | choice-free |
| 11 | Understandability | `no_trivial_understanding` | constructive |
| 12 | Improvability | `goal_is_external` | choice-free |

The ontological core is constructive or choice-free; only Evolution (#6) and Information (#7) reach `Classical.choice`. For #12 the core claim is choice-free — only the prime-cycle separation witness (`cyclic3_no_directed_improvement`) goes classical. Whether that dependence is essential or incidental is an open question (companion doc).

## The structure behind the list

- **K ≅ 2 (the walking arrow):** modelling (#9), governing (#8), and understanding (#11) are the same morphism `R → T` — "a good regulator contains a model" is the internal model is the dual of understanding.
- **The agential split:** 10 ontological principles (what systems *are* and *do*) + 2 agential (#11 *observe*, #12 *intervene* — what an *agent* does *with* a system). The agential pair is independent of system complexity.
- **The blind/directed axis:** #6 (environmental, blind selection) vs #12 (mental, directed goal) — one shared ontogenic skeleton, neither reducible to the other. *Seam:* a system can be evolvable yet not improvable (the prime-cycle).
- **Where "complex adaptive" actually begins:** not at #6. The demandingness gradient is ontological core (any system) → regulation (#8) → models (#9, #10) → agency (#11, #12), with #6 a near-universal blind axis. (Companion finding #19.)

### Corrections to Mobus's informal labels
- #11 is **not** a corollary of #9 (it adds a compression axiom #9 lacks).
- #12 is **not** a corollary of #6 (it adds an external goal + a model #6 lacks).
- #5 **is** a theorem, not an axiom (it derives from #1+#2+#3).

## Changelog
- **2026-08-09 — membrane-crossing seam / interface decomposition** (`Systems/Core/InterfaceDecomposition.lean`, SSF #43): **zero new axioms.** `InterfaceDecomposition` extends the decomposition contract to a component that is itself a parent interface — the case `Decomposition` cannot state and bert-core's v1 gate therefore refuses. Crossing bijections `γsrc`/`γsnk` against the parent's `G`-flows at the component, with substance-kind AND environmental-endpoint preservation (`crossing_refines_inflow`/`_outflow`), plus `substitution_sound` over the four-way seam. Separating instances included and proven (`crossing_contract_separates`): a toy Fed Balance Sheet split passes; a child that drops a membrane crossing and a child that re-kinds one are both refused. All results choice-free (`propext` + `Quot.sound` only; the refinement theorems reach `Quot.sound` alone). No change to the 8-axiom count above. Detail: companion doc, "Downstream bindings".
- **2026-07-23 — typed transition** (`Systems/Dynamics/Transition.lean`, #112 Half A step 1): **zero new axioms — axiom-free** (`#print axioms` on `kindCodomain`, `deterministicClosed`, `markovClosed`: no dependencies). Gives a `Dynamics` descriptor its transition, typed by the kind — the coalgebra structure map Mealy-shaped over the ports. `kindCodomain` maps `deterministic ↝ Id`, `markov ↝ Nat-weighted successors` (the #67 finite form, no Mathlib `PMF`), `nondeterministic ↝ finite successor list`. The type is the check: a `Transition d` is a transition of `d`'s kind by construction. Own-the-definition (frontier-council): the codomain functors are BERT's, external frames are comments only. Homogeneous/per-kind — heterogeneous composition is the open frontier (Half B), absent. No change to the axiom count. Detail: companion doc.
- **2026-07-23 — declared Dynamics descriptor** (`Systems/Dynamics/Record.lean`): **zero new axioms — axiom-free** (`#print axioms` on both example descriptors: no dependencies at all). Refines Mobus's opaque `τ` into a typed descriptor over a carrier (support · kind · inputType · outputType · invariants); definitions + two enums + `rfl`/`by decide` examples. Conservative by parametricity — `τ` has no structural role (`Tuple.lean:48`), witnessed by a typechecking `MobusSystem … (Dynamics C) …` example. **Revised after a frontier-council outside pass:** `conservation` cut from the kind enum (it is an invariant, not a functor family); opaque `parameters` removed (typing per-kind needs the endofunctor = #112); `Unit`-defaulted `inputType`/`outputType` ports added for openness-readiness. Descriptor layer only; the coalgebra semantics (endofunctor interpretation, typed parameters, open composition) are bert-lenses#112, downstream. No change to the axiom count above. Detail: companion doc, "Downstream bindings".
- **2026-07-20 — bert-lenses#89 decomposition seam** (`Systems/Core/Decomposition.lean`): **zero new axioms.** Seam structure + substitution soundness proven fully, assembly proven at depth 1; all results choice-free (`propext` + `Quot.sound` only). No change to the 8-axiom count above. Detail: companion doc, "Downstream bindings".
