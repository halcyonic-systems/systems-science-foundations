# Foundations for Mathematical Systems Science

Machine-verified formalization of seven systems science traditions in Lean 4, discovering their shared categorical structure. They build the future of systems theory. This audits its past.

**~14,400 lines | 74 files (counted 2026-09-03) | zero `sorry`s | zero custom axioms | 7 traditions | K ≅ 2 | all 12 principles formalized: 4 primitives + 2 refinements + 2 stances + 4 theorems (computed 2026-09-04)**

## The Result

Seven definitions of "system," developed independently across six decades (Klir 2001, Bunge 1979, Mesarovic 1975, Wymore 1993, Joslyn 1995, Mobus 2022, Myers 2023), all embed a single categorical structure — the walking arrow **2** — injectively on objects (`klirTo*_obj_injective`). The embeddings are also faithful, but that is a property of the source, not evidence about the targets: **2** is thin, so *every* functor out of it is faithful. The content lives in object-injectivity. The irreducible content of "system" shared by every tradition is one morphism: *relations depend on things*.

The old maximality claim ("nothing larger embeds into all seven") was **false**, and the counterexample is now machine-checked: the fork shape has three objects and embeds into all eight free categories injectively-on-objects and faithfully (`SharedPrimitive.free_category_maximality_fails`). It slips into Joslyn through a *path*, `controller → effector → controlled`, a composite no tradition asserts.

The claim holds one level down, on the generating quivers rather than their free categories. There, two edges of any embedding either coincide or share no vertex (`SharedPrimitive.edges_coincide_or_disjoint`), so a connected quiver has exactly one edge: **the only dependency all eight traditions directly assert is one.** Joslyn and Willems alone force this; the other six are not needed. The result is relative to the documented presentations, which is a real limitation and is stated as one in `Systems/Category/SharedPrimitive.lean`.

The dependence also runs the other way. From the kernel alone, each tradition's presentation is *generated* as a faithful view, and the round trips are identities — the traditions are views of one invariant, not independent ontologies that happen to agree. The kernel was discovered by comparison, but it is logically prior: comparison detects the invariant; the invariant explains the convergence. What generation costs is explicit and machine-checked: the Bunge view requires a bond between distinct components; the Mobus view forbids self-dependency.

An eighth tradition (Spivak 2026, energy-driven systems, added at the same standard) sharpened what "cost" means. Bunge's bond and Mobus's irreflexivity are *conditions* the kernel may already satisfy; Spivak's value channel — a potential driving the dynamics — is *data* the kernel can never supply. Every kernel-generated Spivak view is provably potential-free and static. Said without the machinery: bare relational structure contains no reason for anything to move. "Why" is not hiding inside "how" — it must be paid for from outside, and both directions are machine-checked (the kernel alone lands in the degenerate stratum; a supplied potential escapes it over the same kernel).

Three orientations emerge from the encoding:
- **Structural** (Klir, Bunge, Mobus): arrows converge inward toward components
- **Operational** (Mesarovic, Wymore, Myers): arrows radiate outward from state
- **Cybernetic** (Joslyn): arrows form a cycle — the only tradition with feedback in its shape category

## The Three Frameworks

Each tradition adds structure to the one before it. The formalization encodes all three faithfully and proves they compose.

| Tradition | Definition | What it captures |
|-----------|-----------|-----------------|
| **Klir** (2001) | `S = (T, R)` | Things and a relation. The simplest possible system. |
| **Bunge** (1979) | `⟨C, E, S⟩` | Adds environment as first-class. Three coherence constraints. |
| **Mobus** (2022) | 8-tuple | Adds flows, boundary, milieu, transforms, history, time. Five coherence constraints. |

The commuting triangle proves: Mobus → Bunge → Klir = Mobus → Klir. The proof is `rfl` — the type-checker confirms without reasoning. Neither Bunge nor Mobus knew their frameworks were this compatible.

## Reading the Work

| Resource | Description |
|----------|-------------|
| [Interactive Verso Document](https://halcyonic.systems/systems-ontology/verso/) | Full narrative across six chapters with hoverable Lean proofs |
| This repository | Lean 4 source, CQL schemas, and documentation |

To build the Verso document locally: `cd docs/verso && lake build proposal && lake exe proposal`

## Headline Findings

| # | Finding | Proof method |
|---|---------|--------------|
| 1 | **Common core**: K ≅ **2** embeds into all 8 shape categories, injective on objects (faithfulness is automatic — **2** is thin, so every functor out of it is faithful) | Functor construction + `klirTo*_obj_injective`; faithfulness via `faithful_of_subsingleton_hom` |
| 1b | **Shared primitive**: the only dependency all 8 traditions *directly assert* is one edge (forced by Joslyn + Willems alone) | Quiver-level obstructions, `edges_coincide_or_disjoint` |
| 2 | **Commuting triangle**: Mobus → Bunge → Klir = Mobus → Klir | `rfl` (definitional equality) |
| 3 | **Bunge's 47-year error**: Def 1.6 (*Treatise*, Vol. 4, 1979) says "reflexive, asymmetric" — contradictory; correct: antisymmetric | Compiler rejection |
| 4 | **Statics-dynamics divide**: Mobus → Myers comparison functor — `update` has no preimage | Empty fiber |
| 5 | **Boundary completeness**: "all interaction mediated by boundary" is derived, not axiomatized | Structural consequence of bipartite constraint |
| 6 | **Bridge factorization**: `toBunge = toRichBunge ⋙ flatten` | Functor composition |
| 7 | **Joslyn incomparability**: cyclic shape generates infinite hom-sets; no faithful functor to any acyclic tradition | Open problem (traces, operads, double categories as candidates) |
| 8 | **Unconditional composition**: system composition is valid at both CES and 8-tuple levels without interaction hypotheses | Coherence proofs don't reference cross-system data |
| 9 | **Complexity is not an axiom**: structural measures derive from Systemness + Hierarchy (Networks' relational data is Systemness's `structure'` field; import audit 2026-09-03) | Complexity.lean compiles with only Core imports |
| 10 | **Simon's named gap**: near-decomposability → time-scale separation requires an unstated StrictAnti assumption | Conditional theorem isolates the bridge |
| 11 | **Timescale decomposition**: coupled dynamics decomposes into fast (within-module) and slow (between-module) around equilibria | Fast equilibria = product equilibria (by rfl) |
| 12 | **View generation**: the kernel alone generates the Klir/Bunge/Mobus presentations as faithful views; round trips are identities; the preconditions (Bunge: bond, Mobus: irreflexivity) are the costs of each view | Sections with `rfl` round trips + view coherence triangle |
| 13 | **No teleonomy in the kernel**: every kernel-generated Spivak (energy-driven) view is provably potential-free and static — value/drive is *data* (T, R) cannot supply, not a condition it might satisfy; a supplied potential escapes the stratum over the same kernel | Unconditional view + Def 5.3.2 classifier Props; axioms: `Quot.sound`/`propext` only |

## Principles Axiomatization

Mobus lists 12 principles of systems science. We tested which are independent axioms and which are theorems — the first systematic axiomatization attempt.

**Status**: all 12 resolved (zero `sorry`). **Computed count (2026-09-04, independence matrix + environment build):** the twelve principles are **four ontological primitives** (#1 Systemness, #4 Dynamics, #6 Evolution as `EvolutionE` with environment-relative fitness, #8 Governance as `HomeostatD` with a disturbance input) + **two structural refinements of Systemness** (#3 Networks = the bond graph read as a flow graph; #2 Hierarchy = decomposition + within>between strength, presupposes #1 by construction) + **two agential stances** (#11 Understandability, #12 Improvability in `DirectedAgent`/`DirectedUnderModel` form; bare `Improvement` retired as vacuous) + **four theorems** (#5 from #1+#2, #3's data being #1's field; #7 information, Shannon as a bounded special case; #9 internal models lift to all horizons; #10 self-models as the diagonal of #9). One stated condition: #8's independence from #6 holds provided evolution's criterion is external (Mobus's "not resident in some mind"); with the fitness family free, every governing law is also environment-evolving (`evolvesByEnv_settle`).

*History.* "Eight axioms + four theorems" was the headline from 2026-06-09 to 2026-09-03. The eight structures still exist and are pairwise distinct, but the within-block independence matrix (`Systems/Principles/Matrix.lean`, 2026-09-03) showed that as encoded #3 is #1 read twice, #2 presupposed nothing as a bare relation, bare #12 coincided with non-degenerate #4, and #8 derived #6. The re-headlined #2, the environment coordinate, and the tracking form of #12 (2026-09-04) give the count above; "twelve → ≤11" is superseded.

| # | Principle | Verdict | Key result |
|---|-----------|---------|------------|
| 1 | Systemness | **Primitive** | Composition closure unconditional at CES and 8-tuple levels; the field #3 and #2 refine |
| 2 | Hierarchy | **Refinement of #1** | `Hierarchical` (Mobus Eq. 4.3 decomposition + Simon within>between strength, `Principles/Hierarchy.lean`); presupposes #1 by construction, can fail (`not_hierarchical_of_uniform`); Simon's StrictAnti bridge named |
| 3 | Networks | **Refinement of #1** | The bond graph read as a directed flow graph (`ConcreteSystem.toFlowNetwork`, derivable both ways); adds only the capacity type |
| 4 | Dynamics | **Primitive** | DynamicSystem, coupled dynamics, equilibrium, Flow, timescale decomposition; `sep_dynamics_evolution` |
| 5 | Complexity | **Theorem** | Structural measures derive from #1+#2 (#3's data is #1's `structure'` field). The first reduction found (2026-05). |
| 6 | Evolution | **Primitive** | `EvolutionE`: fitness indexed by a stepping environment (frozen case = old `Evolution`); Red Queen 4-cycle evolves under no fixed order (`redQueen_evolutionE_not_evolution`); `evolvable_but_not_improvable` (#6 ⇏ #12) |
| 7 | Information | **Theorem** | Difference-that-makes-a-difference; Hartley nonspecificity; Shannon bounded (`entropy ≤ hartley`) |
| 8 | Governance | **Primitive** (conditional) | `HomeostatD` with disturbance input (`Robust`); separated from #6 both ways (`sep_governanceD_evolutionE`, `sep_evolutionE_governanceD`) provided fitness is external; Conant-Ashby → K ≅ 2 |
| 9 | Internal Models | **Theorem** | Simulation lifts to all horizons; model map = good-regulator homomorphism, so #9 supplies #8 |
| 10 | Self-Models | **Theorem** | Diagonal case of #9; existence trivial (identity), content is faithfulness |
| 11 | Understandability | **Agential stance** | Strictly-simpler model (onto, lossy, non-degenerate); independent of #9 (two witnesses); non-constant form `UnderstoodNC` restores the #6/#8 ⇏ #11 separations |
| 12 | Improvability | **Agential stance** | `DirectedAgent`/`DirectedUnderModel`: an agent with an understanding rewrites dynamics toward an external goal; bare `Improvement` retired (`improved_iff_moving`); #12 ⇏ #6 (prime-cycle) |

**Foundational profile** (`scripts/axiom-profile.sh`): `#print axioms` on each headline theorem classifies it `constructive` / `choice-free` / `classical`. The ontological core is constructive; only Evolution (#6) and Information (#7) reach `Classical.choice`. The kernel-computed analogue of a "proof vector" (cf. arXiv:2504.00063), but dependencies are computed, not asserted.

**Front door: `Systems/Principles.lean`** — one re-export per principle in Mobus's order, each with its full signature, plus the checked non-derivability witnesses; `#print axioms` on any line reproduces the profile below. The count itself is computed in `Systems/Principles/{Witnesses,Matrix,Hierarchy,NonDegenerate,EnvRelative}.lean` (separating instances, the within-block independence matrix, the re-headlined #2, the non-degeneracy check, the environment-relative #6 and #8) over `Systems/Core/{JointState,EnvState}.lean` (the adopted component–state bridge and the environment coordinate). See `docs/paper/axiom-table.md` (clean reference + profile), `docs/paper/independence-matrix.md` (the matrix, cell by cell), `docs/reference/component-state-bridge-memo.md` (the bridge decision), `docs/paper/dependency-dag.mmd` (the systems-level dependency graph), `docs/reference/principles-formalization-companion.md` (full findings), and `docs/paper/p3-reading-edition.md` (the integrated reading edition).

## Known Limits

- **Quantitative dynamics**: multi-timescale convergence needs metric space infrastructure (structural skeleton is complete).
- **Rule/law distinction**: `ActsOn` is opaque — can't distinguish contingent from necessary relations.
- **Control**: Governance (#8) is formalized as a primitive (`HomeostatD`), separated from Evolution only under an external fitness criterion. Connecting to ShapeJoslyn categorically (the cycle IS the feedback loop) is future work.
- **Variety measures**: Joslyn's dimensional/cardinal variety has no formalization yet.

## Project Structure

```
Systems/
  Core/           Bunge CES + Principles formalization
                  Thing → Bond → System → Level → Assembly → Selection → State
                  → Systemness → Complexity → Dynamics
  Mobus/          8-tuple, flows, boundary, bridge to Bunge, 8-tuple composition
  Klir/           S=(T,R) — common root, commuting triangle (rfl)
  Category/       Shape categories (7), comparison functors, K ≅ 2
  Bunge/          Experimental (StructureFamily, not imported)
  Examples/       Thermostat
docs/
  INDEX.md        Reading order for all documentation
  paper/          Axiom table (+ foundational profile), dependency DAG, outline
  reference/      Technical docs (companion, roadmaps, Simon analysis)
  publications/   AITP 2026, ISSS 2026 abstracts
  verso/          Verso interactive document (6 chapters)
cql/              CQL categorical database schemas
scripts/          axiom-profile.sh (foundational-purity profile) + tooling
```

## Building

Requires Lean 4 (v4.28.0) and Mathlib:

```bash
lake update   # fetch Mathlib (first time only)
lake build    # compile all modules — zero errors, zero sorrys
```

## Related

- [BERT](https://github.com/halcyonic-systems/bert) — Systems analysis tool implementing Mobus's framework. The coherence constraints Lean verifies (disjointness, bipartiteness, boundary completeness) are the grammar rules BERT's System Language compiles from.

## Downstream Consumers

- **mathematical-systems** (private, pre-publication) — atlas of applied systems; each entry carries declaration-level pointers into this repo, resolved by its lean bridge at build time against a pinned commit.
- **protocols-are-systems** (private, pre-publication) — applied protocol instances; depends on this repo as a pinned lake dependency, with three verified protocol instances so far.
- **bert-lenses** — planned consumer of the shape ladder (Klir/Bunge/Mobus) as its structural authoring core.

## Methodology

Built in collaboration with Claude Code (Anthropic). Human editorial judgment and domain interpretation; LLM Lean syntax fluency and tactic generation; compiler final authority on every claim.

## License

MIT
