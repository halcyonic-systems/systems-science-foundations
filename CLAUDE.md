# Systems Ontology --- Lean 4 Formalization

Machine-verified systems ontology in Lean 4 with Mathlib. Seven traditions (Klir, Bunge, Mobus, Myers, Wymore, Mesarović, Joslyn) encoded as shape categories with comparison functors and a common core theorem. ~6,330 lines, zero `sorry`s.

**Key insight**: The common core of all seven independently developed systems definitions is Klir's S = (T, R) --- the walking arrow category **2**. A system, in the sense shared by every tradition from Mesarović (1964) through Myers (2023), is a morphism: relations depend on things. Everything else --- environment, boundary, state, input, output, time, mechanism, feedback --- is tradition-specific elaboration. This was *discovered* through formalization, not claimed by any author.

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
  Core.lean              Imports all Core modules
  Mobus/                 Phase 2: Mobus 8-tuple + composition
    FlowNetwork.lean     Directed graphs with parametric capacity κ (Eq. 4.4)
    Environment.lean     E = ⟨O, M⟩ with parametric milieu (book-revisions)
    Boundary.lean        B = ⟨P, I⟩, boundary completeness (Eq. 4.6)
    Interface.lean       Bipartite flow predicate, source/sink classification
    Tuple.lean           Full 8-tuple, 5 coherence constraints (Eq. 1)
    Bridge.lean          toBunge projection, subsystem preservation, info loss
    Composition.lean     8-tuple composition, bipartite transfer theorem
  Klir/                  Phase 3: Klir common root (146 lines)
    KlirSystem.lean      S = (T, R), projection maps, commuting triangle (rfl)
  Category/              Categorification Phases 1-2 (~2,350 lines)
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
    ShapeComparison.lean    I_Mobus → I_Bunge: faithful, not full, divergence catalogue
    ShapeComparison_Myers.lean   I_Mobus → I_Myers: expose only, update unreachable
    ShapeComparison_Wymore.lean  I_Wymore → I_Mobus: object-injective, time mediated
    Diagram.lean            BungeDiagram: system-as-functor I_Bunge → Type
    CommonCore.lean         K ≅ 𝟐: Klir embeds into all 7 shapes (common core theorem)
Systems.lean             Root import
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
lake build          # Must pass with zero errors, zero sorrys
```

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
  ShapeMesarovic, ShapeJoslyn — all independent (Mathlib only)
  ShapeComparison imports ShapeBunge + ShapeMobus
  ShapeComparison_Myers imports ShapeMobus + ShapeMyers
  ShapeComparison_Wymore imports ShapeWymore + ShapeMobus
  Diagram imports ShapeBunge + Core/System
  CommonCore imports all 7 shape categories
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
9. **Common core theorem** (CommonCore.lean) --- K ≅ **2**: Klir's walking arrow embeds faithfully into all 7 shape categories. The irreducible categorical content of "system" across 60 years of independent traditions is a single morphism: relations depend on things.
10. **Shape category landscape** (Shape*.lean) --- 7 traditions encoded as free categories on dependency quivers; structural/operational/cybernetic divide diagnosed by arrow direction
11. **Statics vs dynamics** (ShapeComparison_Myers.lean) --- Mobus→Myers: all structural constraints map to `expose`; `update` has no preimage. Mobus captures what systems ARE, Myers captures how they BEHAVE.
12. **Temporal mediation** (ShapeComparison_Wymore.lean) --- Wymore→Mobus: object-injective, but `stateOnTime` requires length-2 path through boundary. Mobus mediates time through interface structure.

## Venue Milestones

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

- [bitcoin-bra](../bitcoin-bra/) --- BRA formalization (~1080 lines, 11 files, Lean 4, targeting CPP 2027). Shares `categorification-roadmap.md` — Phase 2 adds categorical functor infrastructure to bitcoin-bra.
- [BERT](https://github.com/halcyonic-systems/bert) --- systems analysis tool implementing Mobus's framework
