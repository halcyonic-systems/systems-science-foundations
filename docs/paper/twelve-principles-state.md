# The twelve principles, as the kernel counts them — state of the result

*A one-page account of Program 2's outcome as of 4 September 2026, with the two figures. The page is `twelve-principles-state.html` (open it in a browser; the figures render there). This file is the same content as text, so it can be read, searched and diffed in the repository. Every Lean name below was checked against `Systems/` on 2026-09-19.*

## Where this sits

| Artifact | What it is |
|---|---|
| [`twelve-principles-state.html`](twelve-principles-state.html) | The page: the count, the four-step pipeline, Figure 1 (dependency graph, regrouped), Figure 2 (the two carriers and the bridge), the table of Lean homes, what checking found, what is open. Self-contained; figures render from the Mermaid sources embedded in it. |
| [`dependency-dag.mmd`](dependency-dag.mmd) | Figure 1's source, kept in step with the page (regrouped 2026-09-04: 3 and 2 hang under 1 as refinements; 3→8 redrawn from 1; 6 and 8 joined by a two-way separation with the external-criterion condition). |
| [`two-carriers.mmd`](two-carriers.mmd) | Figure 2's source. |
| [`p3-reading-edition.md`](p3-reading-edition.md) | The ledger this page summarizes. |
| [`independence-matrix.md`](independence-matrix.md), [`axiom-table.md`](axiom-table.md) | The within-block matrix cell by cell; the clean reference table and axiom profile. |
| [`../reference/component-state-bridge-memo.md`](../reference/component-state-bridge-memo.md) | The bridge decision behind Figure 2. |
| Private interactive copy | https://claude.ai/code/artifact/e562fed0-60c5-4b59-8481-0640e40961f1 (same content; the HTML here is the version of record). |

## The count

Twelve prose principles were given tractable Lean cores, then forced to separate. What survived is not "eight independent axioms." It is:

- **4 ontological primitives**: Systemness, Dynamics, Evolution, Governance.
- **2 refinements of Systemness**: Networks, Hierarchy.
- **2 agential stances**: Understandability, Improvability.
- **4 theorems**: Complexity, Information, Internal Models, Self-Models.

**One condition.** Governance is independent of Evolution provided evolution's criterion is external, Mobus's "not resident in some mind." Let the fitness order float and every governing law is also evolving, by choosing "the set point is fittest." A homeostat is selection with the criterion internalized and frozen; that is Ashby's claim, now `sep_governanceD_evolutionE` and `evolvesByEnv_settle` side by side.

## How prose became checkable: four steps, four owners

1. **The sentence.** Mobus's one-liner, verbatim, in each structure's docstring with its source line. Owned by the author.
2. **The tractable core.** A Lean structure whose fields are the sentence's nouns and whose constraints are its verbs, with named deferrals. Model-drafted, human-read.
3. **Consequences and cases.** Derivations, separating instances, inhabitation witnesses. The only step the kernel guarantees.
4. **The author's audit.** Co-authorship, or a faithfulness ask. The only check on whether the trail leads to what was meant.

## Figure 1: the dependency graph, regrouped

Source: `dependency-dag.mmd`. Solid arrows: derives from, or refines (a theorem or a construction). Dashed: presupposes (a Lean field or def). Fine dotted grey: conjecture with no Lean home (5 → 11). Amber dashed: separated both ways given an external criterion (6 – 8).

What changed since the first draft: Networks and Hierarchy hang under Systemness as refinements (the bond graph read twice; a decomposition whose complex components are themselves systems). The Networks-to-Governance arrow had no Lean home and is redrawn from Systemness. Evolution and Governance are joined by a two-way separation rather than an arrow, with the external-criterion condition on it.

## Figure 2: the two carriers, and the bridge

Source: `two-carriers.mmd`. The component carrier is a type α with a relation (1, 3, 2, and the theorem 5). The state carrier is a joint state with a law (4, 6, 8, the stances 11 and 12, and the theorems 9, 10, 7). The bridge, `JointStateE`, is one coordinate per component, per flow, per environment thing; a lawful subset; aggregate = law factors.

The bridge is adopted. A state is one reading per component, per flow, and per environment thing, which is Bunge's state function indexed by Mobus's tuple and what George's H notes call the state image. Bunge's "union" sentence on page 640 was the one reading that disagreed with the rest of the tradition and with his own three-neuron example (eight states, at most six by union): `union_misses_neuron_aggregate`. The union definitions survive under retired names with tombstones.

## The twelve, with their Lean homes

| # | Principle | Verdict | Structure or theorem | Where it separates, or why it doesn't |
|---|---|---|---|---|
| 1 | Systemness | primitive | `ConcreteSystem` | Composition organized: `composition_organized` |
| 3 | Networks | refinement | `FlowNetwork` · `ConcreteSystem.toFlowNetwork` | Derivable both ways from 1; adds only the capacity type |
| 2 | Hierarchy | refinement | `Hierarchical` (Eq. 4.3 `RecursiveComponent` + `NearDecomposable`) | Presupposes 1 by construction; can fail: `not_hierarchical_of_uniform` |
| 4 | Dynamics | primitive | `DynamicSystem` · `coupled_equilibrium_iff_fixed` | `sep_dynamics_evolution`, `sep_dynamics_governanceNeg` |
| 6 | Evolution | primitive | `EvolutionE` · `redQueen_evolutionE_not_evolution` | Red Queen climbs relative to each environment, evolves under no fixed order; the frozen case is the old structure |
| 8 | Governance | primitive (conditional) | `HomeostatD` · `Robust` | `sep_governanceD_evolutionE`, `sep_evolutionE_governanceD`; condition: `evolvesByEnv_settle` |
| 11 | Understandability | stance | `Understanding` · `UnderstoodNC` | Non-constant model dynamics turns four cardinality separations into dynamical ones |
| 12 | Improvability | stance | `DirectedAgent` · `DirectedUnderModel` | Bare `Improvement` retired: `improved_iff_moving`; the tracking form separates on the 4-cycle |
| 5 | Complexity | theorem | `sameKind_equivalence` | From 1 and 2 by import; 3's data is 1's field |
| 7 | Information | theorem | `entropy_le_log_card` | Shannon bounded by Hartley, equality at uniform |
| 9 | Internal Models | theorem | `AnticipatoryModel.tracks` | One-step correct is correct at every horizon |
| 10 | Self-Models | theorem | `FastSelfModel.accurate_forces_periodic` | Diagonal of 9; accurate fast self-model forces periodicity |

## What the checking found that the prose never contained

- **Evolvability was a property of the environment's order alone** as first encoded (`evolvable_iff_exists_lt`). The repair, fitness indexed by a stepping environment, made dynamics matter and produced the Red Queen.
- **Understanding was satisfied by a model that predicts nothing** on any finite system with three or more states. Non-constant model dynamics is the minimal repair.
- **Hierarchy on Bunge's ancestor relation asserts nothing**; on Mobus's own Equation 4.3 it can fail, and it presupposes systemness because a complex component is a system.
- **The state-space "union" reading of Bunge** misclassifies his own paradigm aggregate. The product reading is what Klir, Mesarovic, Wymore, Willems, Myers, and the bert-compose simulator all use.
- **Whether flows carry state is a Δt question.** A flow with transport time is a stock in transit; if the tick is shorter than the crossing, the flow needs its own coordinate. The tuple's eighth slot decides the shape of the state space.

## Still open

- **Cross-block independence** (component principles against state principles) is now statable through the bridge and has not been run.
- **The compression arrow** from Complexity to Understandability stays a conjecture until someone states it over the joint state.
- **For George:** cite Bunge's page 640 "union" as a slip corrected by his own examples, or derive the product from his definition on histories; and adopt the two-sense vocabulary his own H notes use, structural state (the tuple) and dynamical state (the image).
- **For Facets:** name bert-compose's per-tick row as the state image contract (facets#373).

## Keeping the page honest

The page states the result as of the 4 September push. If a principle's verdict or Lean home changes, change it in three places: the Lean source, `p3-reading-edition.md`, and this page (the HTML and this file carry the same table; `dependency-dag.mmd` and `two-carriers.mmd` are the figure sources, and the HTML embeds copies of them). The names in the table were verified present in `Systems/` on 2026-09-19 by a plain search; a name that disappears from the tree should be marked here rather than silently repaired, as the reading edition's §9 and §10 do.
