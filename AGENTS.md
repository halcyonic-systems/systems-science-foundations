# Systems Ontology --- Lean 4 Formalization

Agent instructions for this repo, for any coding agent. Claude Code reads this file through `CLAUDE.md`, which imports it.

Machine-verified systems ontology in Lean 4 with Mathlib. Shape categories for Klir, Bunge, Mobus, Myers, Wymore, Mesarović, Joslyn, Spivak, Willems, Rosen and Bertalanffy, with comparison functors and the common-core result (existence proven; a quiver-level sharing result in place of the refuted maximality claim, see Claim hygiene). **All 12 Mobus principles formalized** (#6 Evolution completed the set, 6/09). 86 Lean files, ~18,700 lines (counted 2026-10-05), zero `sorry`s, zero custom axioms.

**Claim hygiene**: faithfulness of the eight `klirTo*` embeddings is now a theorem (`klirTo*_faithful`), and the proof is cheap — it follows from `I_Klir` being thin, so it says nothing about the target traditions. The old maximality claim was false; the counterexample is machine-checked in `SharedPrimitive.lean`. The repaired claim lives on quivers, not free categories, and is relative to the documented presentations: `SharedPrimitive.connected_is_single_arrow` ("the only dependency all the encoded traditions directly assert is one", `CommonCore.lean`), forced by Joslyn (no vertex of out-degree two) and Willems (no vertex of in-degree two, no composable pair). Never state maximality at the free-category level. The prose account is `docs/reference/common-core-theorem.md` (revised to the repaired claim 2026-07-25); since 2026-08-11 its headline claims are restated with full types in `Systems/Challenge.lean`, checked by `scripts/check-challenge.sh`.

**Key insight**: Klir's S = (T, R) --- the walking arrow category **2** --- embeds, injective on objects, into eight encoded shapes: Bunge, Mobus, Myers, Wymore, Mesarović (global-state form, Def. 1.4; his I/O form, Def. 1.2, has no arrow), Joslyn, Spivak and Willems (`klirTo*_obj_injective`; `klirTo*_faithful` is free because the source is thin). They are not eight independent witnesses: as shapes I_Willems ≅ I_Mesarovic (`willemsToMesarovic`), and Spivak shares community and lens machinery with Myers. Compared on generating quivers, and relative to the documented presentations, a connected quiver with an edge that embeds into both the Joslyn and the Willems quiver has exactly two vertices, every edge running x → y (`connected_is_single_arrow`; with `no_parallel`, a single edge). Read as the shared commitment, from Mesarović (1964) through Spivak (2026): a system has things and relations among them, and the relations depend on the things. No other directly asserted dependency is common to all eight; environment, boundary, state, input, output, time, mechanism, feedback are tradition-specific elaboration at that level. This was *discovered* through formalization, not claimed by any author.

## Project Structure

```
Systems/
  Core/                  Phase 1: Bunge + Principles formalization
    Thing.lean           Things, parthood, composition (§1.1-1.2)
    Bond.lean            ActsOn, bonding, bondage (§1.2, §2.2)
    System.lean          ConcreteSystem ⟨C,E,S⟩, subsystem order (Def 1.1-1.7)
    Level.lean           Level precedence, NearDecomposable, Simon conditional (Def 1.8, Eq 4.3)
    Assembly.lean        Assembly, emergence as set operations (Def 1.12-1.14)
    Selection.lean       Selective action, composition theorem (Def 1.15, Thm 1.2)
    State.lean           State function, event space, history (§2.2)
    Systemness.lean      RecursiveSystem, composition closure, organized/aggregate (Principle 1)
    Complexity.lean      SameKind equivalence, derivability proof (Principle 5 → theorem)
    Dynamics.lean        DynamicSystem, coupled dynamics, Flow, TimescaleDecomposition (Principle 4)
    Lens.lean            Bidirectional lenses, composition, Conant-Ashby skeleton (Principle 8 bridge)
    Governance.lean      Homeostat, GovernanceSubsystem, TwoLevelGovernance/HCGS (Principle 8)
    InternalModel.lean   InternalModel, tracks (simulation lifts to all horizons), → Conant-Ashby (Principle 9)
    GoodRegulator.lean   Conant-Ashby entropy engine (negMulLog_transfer), outcome distribution (Principle 8/9)
    SelfModel.lean       SelfModel (diagonal of #9), self-anticipation, accurate set invariant (Principle 10)
    Information.lean     Genus (difference-that-makes-a-difference) → Hartley → Shannon as bounded special case (Principle 7)
    Understanding.lean   Compression core: onto+lossy+non-degenerate abstraction (Principle 11), tracks/predict, card/Hartley drop, #9⇏#11 via one-state + Fin 3 prime-cycle witnesses — axiom-tier, dual to #9
    Improvability.lean   Agency framing (Principle 12): Improvement/DirectedAgent — external goal + intervention on dynamics; #12⟹#11 (carries Understanding), Homeostat the engine, #12⇏#6 (prime-cycle no directed agent); #11 GET + #12 PUT = agential layer — axiom-tier
    Evolution.lean       Blind pillar (Principle 6): Evolution over an environmental fitness preorder — generational step fitness-non-decreasing; adapts (all-horizon), Evolvable (CAES capacity); evolvable_but_not_improvable (#6⇏#12, prime-cycle); no model/goal — blind dual of #12 — axiom-tier. Completes all 12.
    Decomposition.lean   Hierarchical decomposition by reference: the seam contract (bert-lenses#89)
    InterfaceDecomposition.lean  Decomposing a BOUNDARY component: the membrane-crossing seam (SSF #43)
    JointState.lean      The component–state bridge: run state as a dependent product indexed by the CES triple
    EnvState.lean        The joint state with an ENVIRONMENT coordinate (decision A, 2026-09-04)
  Core.lean              Imports all Core modules
  Mobus/                 Phase 2: Mobus 8-tuple + composition
    FlowNetwork.lean     Directed graphs with parametric capacity κ (Eq. 4.4)
    Environment.lean     E = ⟨O, M⟩ with parametric milieu (book-revisions)
    Boundary.lean        B = ⟨P, I⟩, boundary completeness (Eq. 4.6)
    Interface.lean       Bipartite flow predicate, source/sink classification
    Tuple.lean           Full 8-tuple, 5 coherence constraints (Eq. 1)
    Bridge.lean          toBunge projection, subsystem preservation, info loss
    Composition.lean     8-tuple composition, bipartite transfer theorem
    Lifecycle.lean       Closure of the 8-tuple under lawful change (the life-cycle paper's centre)
  Bunge/
    StructureFamily.lean Richer Bunge structure: a family of named relations (imported by the Phase 1 functors)
    AggregateBridge.lean SSF #48: the two aggregate criteria, bridge or separating instance
  Klir/                  Phase 3: Klir common root, views, lens-entry gates
    KlirSystem.lean      S = (T, R), projection maps, commuting triangle (rfl)
    ViewGeneration.lean  The K ≅ 2 kernel generates each tradition's presentation as a faithful view
    SpivakSystem.lean    The data-level Spivak view: energy-driven systems and the cost of the eighth entry
    RosenWitness.lean    Mapping 008, claim 3: a Bunge concrete system whose Rosen view loses the bond
    Gates.lean           The lens-entry gate booleans, shared by every binding rung (bert-lenses#24)
    GatesTruthTable.lean Rung 1 of the lens-entry binding: fixture the Rust gates are tested against
    GatesOracle.lean     Rung 1.5: the `lake exe` oracle over the same gate declarations
  Category/              Categorification
    SubsystemCategory.lean  Subsystem orderings as thin categories (Preorder instances)
    FlattenFunctor.lean     Flatten as functor, Finding 3 as naturality
    OrderingTriangle.lean   Three orderings as functor triangle, non-fullness witnesses
    BridgeFunctor.lean      Mobus→Bunge bridge factorization through structure family
    ShapeKlir.lean          I_Klir: 2 obj, 1 arrow (walking arrow)
    ShapeBunge.lean         I_Bunge: 3 obj, 3 arrows (CES dependency quiver)
    ShapeMobus.lean         I_Mobus: 8 obj, 5 arrows + 3 isolated
    ShapeMyers.lean         I_Myers: 3 obj, 2 arrows (lens/deterministic system)
    ShapeWymore.lean        I_Wymore: 4 obj, 3 arrows (FSD quintuple + time)
    ShapeMesarovic.lean     I_Mesarovic: 2-3 obj (I/O base + global state extension)
    ShapeJoslyn.lean        I_Joslyn: 3 obj, 3 arrows (cyclic — feedback loop)
    ShapeSpivak.lean        Shape category for Spivak's adaptive arrangements
    ShapeWillems.lean       Shape category for Willems' behavioral triple Σ = (T, W, B)
    ShapeRosen.lean         Shape category for Rosen's formal system (S, F)
    ShapeBertalanffy.lean   Shape categories for Bertalanffy's GST: the 1968 shape, the 1972 restatement, and the revision functor
    ShapeComparison.lean    I_Mobus → I_Bunge: faithful, not full, divergence catalogue
    ShapeComparison_Myers.lean   I_Mobus → I_Myers: expose only, update unreachable
    ShapeComparison_Wymore.lean  I_Wymore → I_Mobus: object-injective, time mediated
    Diagram.lean            BungeDiagram: system-as-functor I_Bunge → Type
    CommonCore.lean         Existence: I_Klir embeds into 8 shapes, injective on objects + faithful
    SharedPrimitive.lean    Quiver-level sharing result: connected_is_single_arrow; free_category_maximality_fails
    MyersSpivakFaithful.lean     The commitments-ladder inclusion is faithful
    RosenKlirIso.lean       Rosen's (S, F) and the walking arrow are the same shape (mapping 008, claim 1)
    RosenConjugacy.lean     Rosen's conjugacy is the isomorphism relation of the arrow category
    CyclicObstruction.lean  Cyclicity is a boundary of the finite-shape method (shared obstruction)
    JoslynIncomparability.lean   Joslyn's feedback shape is a boundary of the finite-shape method
    SpivakIncomparability.lean   Spivak's value-feedback shape is a boundary of the finite-shape method
  Joslyn/                Joslyn, "Semantic Control Systems" (1995)
    JoslynSystem.lean    Joslyn's System₁: the fourth vertex, set-theoretic tier
    Control.lean         Control₁/Control₂ hierarchy + Prop 29 tractable core
    BungeMap.lean        Phase 4.4: the Joslyn→Bunge partial map, the non-functorial edge
    HCGS.lean            Phase 4.5: Control₂ ≅ HCGS, the independent convergence
  Mesarovic/
    Decomposition.lean   Mesarovic 1964: the decomposition theorem's two cores
  Dynamics/
    Record.lean          The declared Dynamics descriptor: dynamics as checkable data
    Transition.lean      The typed transition (#112 Half A, step 1)
    Mechanism.lean       MechanismSpec: the Increment-1 surrogate for Bunge's mechanism M(σ)
    CircuitHistory.lean  RESEARCH (bert-lenses#112): the H-instantiation question
  Principles/
    Matrix.lean          The within-block independence matrix
    Witnesses.lean       Separating instances for the dependency DAG
    Hierarchy.lean       #2 Hierarchy re-headlined on Mobus Eq. 4.3
    NonDegenerate.lean   The proposed non-degeneracy conditions, as new predicates
    EnvRelative.lean     Environment-relative readings of #6 and #8 on a product carrier S × E
  Examples/
    Thermostat.lean      Joslyn's thermostat formalized under Klir, Bunge, and Mobus
  Principles.lean        Mobus's twelve principles, the front door
  Challenge.lean         The K ≅ 2 headline claims, restated for cold verification
Systems.lean             Root import
(Floridi–Jia–Tohmé 2025 Figure 1 in Lean lives in its OWN repo, halcyonic-systems/floridi-lean,
 Mathlib pinned to this repo's revision; moved out 2026-09-10 so it stays a small citable unit.)
docs/
  verso/                 Verso interactive documents (6-chapter flagship + Building Story)
  publications/          Conference abstracts (AITP, ISSS)
  reference/             Active technical docs, categorification roadmap
  archive/               Historical process docs + original HTML artifacts
cql/                     CQL categorical database schemas
  cql.jar                CQL IDE (Jan 2026 release)
  test_instance.cql      All-in-one: CESM schema + GovGraph schema + functor + test data + sigma
  cesm_ontology.cql      Standalone CESM schema (reference, not runnable alone)
  gov_graph.cql          Standalone GovGraph schema (reference, not runnable alone)
  civic_to_cesm.cql      Standalone mapping (reference, not runnable alone)
  export/                CSV exports from CESMData instance
```

## CQL (Categorical Database Layer)

Schemas as small categories, instances as functors C → Set, migrations as Sigma/Delta/Pi. CQL bridges the Lean proof layer (properties hold for all instances) to real-world data (properties verified for specific instances).

```bash
cql                                    # launch IDE (alias in ~/.zshrc)
cql -i cql/test_instance.cql          # launch with file preloaded
```

**Key design constraint**: CQL's Knuth-Bendix completion requires acyclic FK graphs. Self-referential FKs (A→A) and bidirectional FKs (A→B + B→A) cause infinite path enumeration. Hierarchical relationships (entity parent, budget-meeting links) must be modeled as attributes (strings), not FKs.

**Current mapping** (functor F : GovGraph → CESM):

| Civic concept | CESM entity | Semantic interpretation |
|---|---|---|
| Entity | Component | Government bodies are system components |
| Person | FlowEdge | People are flows (role occupancy) connecting to components |
| Meeting | FlowEdge | Meetings are information/decision flows |
| Document | Relation | Documents are relational artifacts connecting flows |
| Motion | Relation | Motions are acts-on: mover acts on system state |
| BudgetItem | FlowEdge | Budget allocations are resource flows with capacity |

## Build & Verify

```bash
lake build                  # Must pass with zero errors, zero sorrys
scripts/axiom-profile.sh    # Foundational-purity profile of the 12 headline theorems
```

`axiom-profile.sh` runs `#print axioms` on one showcase theorem per Mobus principle and classifies each `constructive` / `choice-free` / `classical` / `UNSOUND` (sorryAx-reaching). It is the kernel-computed analogue of a "proof vector" — dependencies are computed, not asserted. Note: SSF's 8 systems axioms are structures/defs, not Lean `axiom`s, so this is a foundational-purity signal; the systems-level dependency vector lives in `docs/paper/dependency-dag.mmd`. The ontological core is constructive; only Evolution (#6) and Information (#7) reach `Classical.choice`. Full table: `docs/paper/axiom-table.md`.

## Site Deployment

The Verso document and handout are deployed to GitHub Pages via the `gh-pages` branch.

```bash
./deploy.sh         # Build Verso, assemble site, push to gh-pages
```

This builds the Verso document (`docs/verso/`), copies the output alongside `site/handout/` and `site/index.html`, force-pushes to `gh-pages`, and switches back to `main`. One command, ~2 min.

**After any Verso source change** (editing `.lean` files in `docs/verso/SystemsProposal/`), run `./deploy.sh` to update the live site. Source files are committed to `main`; built HTML lives only on `gh-pages`.

## Conventions

- Every definition includes a docstring citing the source (Bunge Def #, Mobus Eq #, or Klir Eq #)
- `autoImplicit = false` --- all universes and variables explicit
- Lean toolchain: v4.28.0 (pinned by Mathlib)
- Zero `sorry`s in committed code
- Mathlib instances preferred over hand-rolled proofs
- Docstrings use "independent convergence" framing, never "Mobus extends/refines Bunge"

## Composability Discipline (Anti-Drive-By-Proving)

Formal artifacts must explain, not just verify. Correct is not composable.

**Lean proofs:**
- Never accept a tactic proof you cannot narrate in one English sentence. If `omega` or `decide` closes a goal and you cannot say *why* it is true, refactor into named lemmas with docstrings.
- Proof structure must mirror mathematical argument structure. The lemma hierarchy is for humans; the tactics are for the compiler.
- No AI-generated proof blocks without human-readable companion explanation at the same granularity.

**CQL schemas** (`cql/`):
- Every entity mapping in a functor must have a semantic interpretation comment: *why* this civic concept maps to this systems concept.
- Schema changes require updating the companion mapping table (in the session file or README), not just recompiling.

**General rule:**
- Proof → docstring. Schema → semantic interpretation. Functor → narrative. The formal artifact verifies; the companion explains. Neither is sufficient alone.
- If the compiler accepts it but you cannot explain it to a collaborator, it is not done.

## Dependency Graph

```
Phase 1 (Bunge):
  Thing ──→ Bond ──→ System ──→ Level, Assembly, Selection, State

Phase 2 (Mobus):
  FlowNetwork ──→ Boundary, Environment, Interface ──→ Tuple ──→ Bridge
  Bridge also imports System (Phase 1)

Phase 3 (Klir):
  KlirSystem imports Bridge (Phase 2) — connects all three frameworks

Categorification Phase 1 (thin categories):
  SubsystemCategory ──→ FlattenFunctor ──→ BridgeFunctor
  SubsystemCategory ──→ OrderingTriangle
  All import StructureFamily (Bunge) + Bridge (Mobus)

Categorification Phase 2 (shape categories — free categories on quivers):
  ShapeKlir, ShapeBunge, ShapeMobus, ShapeMyers, ShapeWymore,
  ShapeMesarovic, ShapeJoslyn, ShapeRosen — all independent (Mathlib only)
  ShapeSpivak imports ShapeMyers
  ShapeWillems imports ShapeKlir + ShapeMesarovic
  ShapeBertalanffy imports ShapeKlir
  ShapeComparison imports ShapeBunge + ShapeMobus
  ShapeComparison_Myers imports ShapeMobus + ShapeMyers
  ShapeComparison_Wymore imports ShapeWymore + ShapeMobus
  Diagram imports ShapeBunge + Core/System
  CommonCore imports ShapeKlir + the 8 target shapes
    (Bunge, Mobus, Myers, Wymore, Mesarovic, Joslyn, Spivak, Willems)
  SharedPrimitive imports CommonCore
```

## Headline Results

1. **Commuting triangle** (KlirSystem.lean) --- Mobus → Bunge → Klir = Mobus → Klir by `rfl`
2. **Bridge theorem** (Bridge.lean) --- every 8-tuple projects to a valid CES triple
3. **Boundary completeness** (Tuple.lean) --- derived from bipartite constraint, not axiomatized
4. **Subsystem preservation** (Bridge.lean) --- partial order transfers through projection
5. **Information loss** (Bridge.lean) --- 6 formally characterized categories of divergence
6. **Error detection** (System.lean) --- Bunge's "asymmetric" corrected to antisymmetric
7. **Bridge factorization** (BridgeFunctor.lean) --- toBunge = toRichBunge ⋙ flatten (Finding 6)
8. **Ordering triangle** (OrderingTriangle.lean) --- family ⟹ refinement ⟹ flat, strict (Finding 8)
9. **Common core** (CommonCore.lean, SharedPrimitive.lean) --- Existence: Klir's walking arrow embeds into 8 encoded shapes, injective on objects (faithfulness is free). Quiver-level sharing result, not a maximality theorem; relative to the documented presentations and for a connected shared quiver: the only dependency all the encoded traditions directly assert is one (`connected_is_single_arrow`), forced by Joslyn and Willems. The free-category version is false (`free_category_maximality_fails`).
10. **Shape category landscape** (Shape*.lean) --- 11 traditions encoded as free categories on dependency quivers (13 shapes, counting Mesarović's I/O and global-state forms and Bertalanffy 1968/1972); structural/operational/cybernetic divide diagnosed by arrow direction
11. **Statics vs dynamics** (ShapeComparison_Myers.lean) --- Mobus→Myers: all structural constraints map to `expose`; `update` has no preimage. Mobus captures what systems ARE, Myers captures how they BEHAVE.
12. **Temporal mediation** (ShapeComparison_Wymore.lean) --- Wymore→Mobus: object-injective, but `stateOnTime` requires length-2 path through boundary. Mobus mediates time through interface structure.

## Venue Milestones (as planned, early 2026)

- **AITP 2026** (May): Extended abstract on LLM-assisted formalization + commuting triangle
- **ISSS 2026** (July): Presentation --- "What happens when you type-check Bunge"
- **JOWO/FOIS 2026**: Formal ontology workshop paper
- **Journal** (late 2026): Full paper with BRA companion

Abstract drafts: `docs/publications/aitp-2026-abstract.md`, `docs/publications/isss-2026-abstract.md`

## Key Source References

- Klir, *Facets of Systems Science* (2001), Eq. 1.1 --- common root
- Bunge, *Treatise on Basic Philosophy* Vol. 4, Ch. 1 (1979) --- CES triple
- Mobus, *Systems Science* Ch. 4 (2022) + book-revisions (2024) --- 8-tuple
- Phase 1 retrospective: `docs/archive/phase1-retrospective.md`
- Architecture decisions: `docs/reference/recursive-component-architecture.md`

## Related Projects

- [bitcoin-bra](https://github.com/rsthornton/bitcoin-bra) --- BRA formalization in Lean 4 (archived locally). Shares `categorification-roadmap.md`.
- [BERT](https://github.com/halcyonic-systems/bert) --- systems analysis tool implementing Mobus's framework
