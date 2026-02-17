# Systems Ontology — Lean 4 Formalization

Formal verification of Bunge's systems ontology (*Treatise on Basic Philosophy* Vol. 4, Ch. 1) and Mobus's computational extensions (*Understanding Systems* Ch. 4) in Lean 4 with Mathlib.

## Status

**Phase 1 complete**: 864 lines, 74 declarations, zero sorrys. Full `lake build` passes.

## What's Here

Seven core modules formalizing the mathematical foundations of general systems theory:

| Module | Lines | Decls | Bunge Reference | Key Content |
|--------|-------|-------|-----------------|-------------|
| Thing.lean | 54 | 5 | §1.1-1.2 | Parthood preorder, composition |
| Bond.lean | 79 | 7 | §1.2, §2.2 | ActsOn relation, bonding, bondage |
| System.lean | 172 | 14 | Def 1.1-1.7 | CES triple, subsystem partial order |
| Level.lean | 137 | 15 | Def 1.8, Eq 4.3 | Level precedence, recursive decomposition |
| Assembly.lean | 134 | 12 | Def 1.12-1.14 | Assembly, emergence as set operations |
| Selection.lean | 128 | 9 | Def 1.15, Thm 1.2 | Selective action, composition theorem |
| State.lean | 141 | 12 | §2.2 | State function, events, aggregate characterization |

## Showcase Theorems

1. **Subsystem is a partial order** — reflexive, transitive, antisymmetric (Def 1.6)
2. **Selection composition** — composed adapted = second selection's adapted (Thm 1.2)
3. **Aggregate characterization** — state space = union of component spaces (p. 640)
4. **Emergence = set difference** — demystifying emergence via set operations (Def 1.13)
5. **Ancestry is transitive** — transitive closure of immediate ancestor (Def 1.16)
6. **Recursive decomposition terminates** — well-foundedness from inductive type (Mobus Eq 4.3)
7. **Universe is only closed system** — complementary open/closed (Cor 1.1)

## Building

Requires Lean 4 (v4.28.0) and Mathlib:

```bash
lake update   # fetch Mathlib (first time only)
lake build    # compile all modules
```

## Dependency Graph

```
Thing.lean ──→ Bond.lean ──→ System.lean ──→ Level.lean
                                  │
                                  ├──→ Assembly.lean
                                  ├──→ Selection.lean
                                  └──→ State.lean
```

## Roadmap

- **Phase 1** (complete): Core ontology — 7 modules, zero sorrys
- **Phase 2**: BRA instantiation — Bitcoin Resource Accounting as `ConcreteSystem` instance
- **Phase 3**: Mobus 8-tuple enrichment `S = ⟨C,N,E,G,B,T,H,Δt⟩`

## Venues

- **May 2026**: AITP abstract + ISSS presentation
- **July 2026**: JOWO/ONTOLLM workshop paper
- **Late 2026**: Journal submission with BRA instance

## Related

- [bitcoin-bra](../bitcoin-bra/) — Bitcoin Resource Accounting formalization (Lean 4), future lake dependency
