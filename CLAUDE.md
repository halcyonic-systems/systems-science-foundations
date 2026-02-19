# Systems Ontology --- Lean 4 Formalization

Machine-verified commuting triangle of systems ontology: Klir's `S = (T, R)` (1969/2001) -> Bunge's CES triple (1979) -> Mobus's 8-tuple (2022). Three independently developed frameworks, one verified diagram. ~2,930 lines, zero `sorry`s.

**Key insight**: Bunge and Mobus both descend from Klir but never reference each other. The compatibility was *discovered* through formalization, not claimed by any author. The `rfl` proofs trace to both inheriting T = `Set α` and R = `Set (α × α)` from Klir without changing the mathematical type.

## Project Structure

```
Systems/
  Core/                  Phase 1: Bunge (864 lines)
    Thing.lean           Things, parthood, composition (§1.1-1.2)
    Bond.lean            ActsOn, bonding, bondage (§1.2, §2.2)
    System.lean          ConcreteSystem ⟨C,E,S⟩, subsystem order (Def 1.1-1.7)
    Level.lean           Level precedence, recursive decomposition (Def 1.8, Eq 4.3)
    Assembly.lean        Assembly, emergence as set operations (Def 1.12-1.14)
    Selection.lean       Selective action, composition theorem (Def 1.15, Thm 1.2)
    State.lean           State function, event space, history (§2.2)
  Core.lean              Imports all Core modules
  Mobus/                 Phase 2: Mobus 8-tuple (886 lines)
    FlowNetwork.lean     Directed graphs with parametric capacity κ (Eq. 4.4)
    Environment.lean     E = ⟨O, M⟩ with parametric milieu (book-revisions)
    Boundary.lean        B = ⟨P, I⟩, boundary completeness (Eq. 4.6)
    Interface.lean       Bipartite flow predicate, source/sink classification
    Tuple.lean           Full 8-tuple, 5 coherence constraints (Eq. 1)
    Bridge.lean          toBunge projection, subsystem preservation, info loss
  Klir/                  Phase 3: Klir common root (146 lines)
    KlirSystem.lean      S = (T, R), projection maps, commuting triangle (rfl)
  Category/              Categorification Phase 1 (~563 lines)
    SubsystemCategory.lean  Subsystem orderings as thin categories (Preorder instances)
    FlattenFunctor.lean     Flatten as functor, Finding 3 as naturality
    OrderingTriangle.lean   Three orderings as functor triangle, non-fullness witnesses
    BridgeFunctor.lean      Mobus→Bunge bridge factorization through structure family
Systems.lean             Root import
docs/                    11 docs: abstracts, StructureFamily findings, reference material, retrospectives
```

## Build & Verify

```bash
lake build          # Must pass with zero errors, zero sorrys
```

## Conventions

- Every definition includes a docstring citing the source (Bunge Def #, Mobus Eq #, or Klir Eq #)
- `autoImplicit = false` --- all universes and variables explicit
- Lean toolchain: v4.28.0 (pinned by Mathlib)
- Zero `sorry`s in committed code
- Mathlib instances preferred over hand-rolled proofs
- Docstrings use "independent convergence" framing, never "Mobus extends/refines Bunge"

## Dependency Graph

```
Phase 1 (Bunge):
  Thing ──→ Bond ──→ System ──→ Level, Assembly, Selection, State

Phase 2 (Mobus):
  FlowNetwork ──→ Boundary, Environment, Interface ──→ Tuple ──→ Bridge
  Bridge also imports System (Phase 1)

Phase 3 (Klir):
  KlirSystem imports Bridge (Phase 2) — connects all three frameworks

Categorification (Phase 1):
  SubsystemCategory ──→ FlattenFunctor ──→ BridgeFunctor
  SubsystemCategory ──→ OrderingTriangle
  All import StructureFamily (Bunge) + Bridge (Mobus)
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

## Venue Milestones

- **AITP 2026** (May): Extended abstract on LLM-assisted formalization + commuting triangle
- **ISSS 2026** (July): Presentation --- "What happens when you type-check Bunge"
- **JOWO/FOIS 2026**: Formal ontology workshop paper
- **Journal** (late 2026): Full paper with BRA companion

Abstract drafts: `docs/aitp-2026-abstract.md`, `docs/isss-2026-abstract.md`

## Key Source References

- Klir, *Facets of Systems Science* (2001), Eq. 1.1 --- common root
- Bunge, *Treatise on Basic Philosophy* Vol. 4, Ch. 1 (1979) --- CES triple
- Mobus, *Systems Science* Ch. 4 (2022) + book-revisions (2024) --- 8-tuple
- Phase 1 retrospective: `docs/phase1-retrospective.md`
- Architecture decisions: `docs/recursive-component-architecture.md`

## Related Projects

- [bitcoin-bra](../bitcoin-bra/) --- BRA formalization (~1080 lines, 11 files, Lean 4, targeting CPP 2027). Shares `categorification-roadmap.md` — Phase 2 adds categorical functor infrastructure to bitcoin-bra.
- [BERT](https://github.com/halcyonic-systems/bert) --- systems analysis tool implementing Mobus's framework
