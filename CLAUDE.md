# Systems Ontology — Lean 4 Formalization

Formalizes Bunge's systems ontology (Treatise on Basic Philosophy Vol. 4, Ch. 1) and Mobus's computational extensions (Understanding Systems Ch. 4, plus book-revisions 8-tuple) in Lean 4.

## Project Structure

```
Systems/
  Core/
    Thing.lean      — Things, parthood, composition (Bunge §1.1-1.2)
    Bond.lean       — Action, bonding, bondage (Bunge §1.2, §2.2)
    System.lean     — ConcreteSystem ⟨C,E,S⟩, subsystem order (Bunge Def 1.1-1.7)
    Level.lean      — Level precedence, recursive decomposition (Bunge Def 1.8, Mobus Eq 4.3)
    Assembly.lean   — Assembly, emergence (Bunge Def 1.12-1.14, Post 1.4-1.5)
    Selection.lean  — Selective action, composition theorem (Bunge Def 1.15, Thm 1.2)
    State.lean      — State function, event space, history (Bunge §2.2)
  Core.lean         — Imports all Core modules
  Instance/         — Phase 2: BRA instantiation
Systems.lean        — Root import
docs/               — Source material extracts
```

## Build & Verify

```bash
lake build          # Must pass with zero errors
```

## Conventions

- Every Lean definition includes a docstring citing the Bunge definition number
- `autoImplicit = false` — all universes and variables must be explicit
- Lean toolchain: v4.28.0 (pinned by Mathlib)
- Zero `sorry`s in committed code
- Mathlib instances preferred over hand-rolled proofs (e.g., `Preorder`, `PartialOrder`)

## Dependency Graph

```
Thing.lean ──→ Bond.lean ──→ System.lean ──→ Level.lean
                                  │
                                  ├──→ Assembly.lean
                                  ├──→ Selection.lean
                                  └──→ State.lean
```

## Venue Milestones

- **May 2026 (AITP + ISSS)**: Thing, Bond, System, Selection — zero sorrys
- **July 2026 (JOWO)**: All 7 files compile, Assembly + State showcase theorems
- **Late 2026 (Journal)**: Phase 2 BRA instance

## Key Source References

- Bunge Ch. 1 definitions: lines 309-950 of vault Bunge file
- Mobus Ch. 4 recursive component: Eq. 4.3
- Book-revisions 8-tuple: `S = ⟨C,N,E,G,B,T,H,Δt⟩`
