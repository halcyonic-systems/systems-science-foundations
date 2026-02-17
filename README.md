# Systems Ontology — Lean 4 Formalization

Machine-verified formalization of three independently developed systems ontology frameworks, proving they form a commuting triangle:

```
        Klir (1969/2001)
       S = (T, R)
      ╱             ╲
    adds E          adds flows, boundary,
  (environment)     milieu, transforms,
    ╱               history, time scale
   ╱                   ╲
Bunge (1979)          Mobus (2022)
⟨C, E, S⟩             ⟨C, N, E, G, B, T, H, Δt⟩
   ╲                   ╱
    ╲    toBunge      ╱
     ╲ ─────────── ╱
      ╲           ╱
       ╲         ╱
        ╲       ╱
    Mobus→Bunge→Klir
         =             ← proof: rfl
    Mobus→Klir
```

Klir defined a system as a set of things and a relation. Bunge added environment. Mobus added typed flows, boundaries, transforms, history, and time scale. Neither Bunge nor Mobus references the other --- they developed independently from the shared Klir root, 43 years apart. The Lean proof assistant confirms: both paths from the 8-tuple back to (T, R) produce *definitionally identical* results. The `rfl` proofs trace to both authors inheriting T = `Set α` and R = `Set (α × α)` from Klir without changing the mathematical type.

This was not claimed by any of the three authors. It was *discovered* through formalization.

## Status

**1,896 lines | 16 modules | 120 declarations | zero `sorry`s**

All three phases complete. Full `lake build` passes.

## What Formalization Revealed

The compiler told us things about these ontologies that decades of reading had not:

- **A logical error in Bunge (1979)**: Def 1.6 describes the subsystem relation as "reflexive, asymmetric, and transitive." A relation cannot be both reflexive and asymmetric. He means *antisymmetric* --- a partial order. In print 47 years. The proof assistant caught it immediately.

- **Cross-volume dependency architecture**: Bunge's Corollary 1.1 ("the universe is the only closed system") is a tautology without Postulate 5.10 from Vol. 3 --- a dependency invisible in the prose numbering but structurally undeniable in the type system.

- **Independent convergence with formally characterized divergence**: Six categories of information in Mobus's 8-tuple have no Bunge counterpart (milieu, capacity, boundary properties, transforms, history, time scale). These mark precisely where the engineering tradition elaborated concepts the philosophical tradition did not require.

- **Clean compositions as empirical findings**: Selection composition (Bunge's Theorem 1.2) proves by `rfl`. Emergence decomposes into set operations via `simp`. Bipartite external flows imply boundary completeness as a free structural consequence. These are not trivially expected --- they confirm that the right mathematical representations make deep theorems definitionally true.

## Modules

### Phase 1: Bunge's Philosophical Ontology (864 lines)

Formalizes *Treatise on Basic Philosophy* Vol. 4, Ch. 1 (1979).

| Module | Lines | Source | Key Content |
|--------|-------|--------|-------------|
| Thing.lean | 54 | §1.1-1.2 | Parthood preorder, composition |
| Bond.lean | 79 | §1.2, §2.2 | ActsOn relation, bonding, bondage |
| System.lean | 172 | Def 1.1-1.7 | CES triple `⟨C, E, S⟩`, subsystem partial order |
| Level.lean | 137 | Def 1.8, Eq 4.3 | Level precedence, recursive decomposition |
| Assembly.lean | 134 | Def 1.12-1.14 | Assembly, emergence as set operations |
| Selection.lean | 128 | Def 1.15, Thm 1.2 | Selective action, composition theorem (`rfl`) |
| State.lean | 141 | §2.2 | State function, events, aggregate characterization |
| + root imports | 19 | | Core.lean + Systems.lean |

### Phase 2: Mobus's Engineering Methodology (886 lines)

Formalizes *Understanding Systems* Ch. 4 (2022), plus 2024 book-revisions.

| Module | Lines | Source | Key Content |
|--------|-------|--------|-------------|
| FlowNetwork.lean | 177 | Eq. 4.4 | Directed graphs with parametric capacity `κ` |
| Environment.lean | 87 | Book-revisions | E = `⟨O, M⟩` with parametric milieu |
| Boundary.lean | 111 | Eq. 4.6 | B = `⟨P, I⟩`, boundary completeness |
| Interface.lean | 137 | Book-revisions | Bipartite flow predicate, source/sink classification |
| Tuple.lean | 168 | Eq. 1 | Full 8-tuple with 5 coherence constraints |
| Bridge.lean | 206 | Original | `toBunge` projection, subsystem preservation, information loss |

### Phase 3: Klir's Common Root (146 lines)

Formalizes *Facets of Systems Science* (2001), Eq. 1.1.

| Module | Lines | Source | Key Content |
|--------|-------|--------|-------------|
| KlirSystem.lean | 146 | Eq. 1.1 | `S = (T, R)`, projection maps, commuting triangle (`rfl`) |

## Showcase Theorems

1. **Commuting triangle** --- Mobus → Bunge → Klir = Mobus → Klir, proof: `rfl` (KlirSystem.lean)
2. **Bridge theorem** --- every Mobus 8-tuple projects to a valid Bunge CES triple (Bridge.lean)
3. **Boundary completeness** --- bipartite external flows imply boundary mediates all interaction, derived not axiomatized (Tuple.lean)
4. **Subsystem preservation** --- bridge preserves subsystem partial order, proof: `⟨hsub.1, hsub.2.1, hsub.2.2⟩` (Bridge.lean)
5. **Subsystem is a partial order** --- correcting Bunge's "asymmetric" to antisymmetric (System.lean)
6. **Selection composition** --- composed adapted = second selection's adapted, proof: `rfl` (Selection.lean)
7. **Emergence = set operations** --- qualitative novelty as symmetric difference, proof: `simp` (Assembly.lean)
8. **Information loss characterization** --- two Mobus systems agreeing on (C, E.objects, totalRelation) project to identical CES triples (Bridge.lean)

## Building

Requires Lean 4 (v4.28.0) and Mathlib:

```bash
lake update   # fetch Mathlib (first time only)
lake build    # compile all 16 modules — must pass with zero errors
```

## Dependency Graph

```
                    Phase 1: Bunge
Thing.lean ──→ Bond.lean ──→ System.lean ──→ Level.lean
                                  │
                                  ├──→ Assembly.lean
                                  ├──→ Selection.lean
                                  └──→ State.lean

                    Phase 2: Mobus
FlowNetwork.lean ──→ Environment.lean
       │                    │
       ├──→ Boundary.lean ──┤
       │         │          │
       │         ▼          │
       ├──→ Interface.lean  │
       │         │          │
       ▼         ▼          ▼
       Tuple.lean ◄─────────┘
            │
            ▼
       Bridge.lean ◄── System.lean (Phase 1)

                    Phase 3: Klir
       KlirSystem.lean ◄── Bridge.lean (Phase 2)
```

## Methodology

This formalization was produced collaboratively between a domain expert and an LLM (Anthropic's Claude) using the Lean 4 proof assistant. The workflow:

- **Human**: editorial judgment, interpretation choices when source text is ambiguous, recognizing when LLM output is type-correct but conceptually wrong
- **LLM**: Lean syntax fluency, Mathlib API navigation, tactic proof generation
- **Compiler**: final authority --- zero `sorry`s means every claim is machine-checked

The hard problems were not proof search (no proof required more than a few tactic steps). They were *representational*: should `ActsOn` reference `HasStateSpace`? Should `environment` be a field or derived? Should we use `Set` or `Finset`? These decisions propagate through the entire codebase and require understanding the source material, not Lean expertise.

## Intellectual Genealogy

```
Klir (1969, 2001) ─── S = (T, R) ─── the seed
   │                                      │
   ├── Bunge (1979) ── cites Klir ────── adds Environment ── philosophical ontology
   │                                      │
   └── Mobus (2022) ── cites Klir ────── adds flows, boundary, milieu ── engineering methodology
                                          │
                              Neither references the other.
                                          │
                         Joslyn (PhD student of Klir)
                                          │
                         Author (student of Joslyn, built BERT on Mobus, formalized Bunge)
                                          │
                         The commuting triangle is the formal structure
                         of an intellectual tradition made visible
                         by a proof assistant.
```

## Operational Grounding

The formalized ontology is not purely theoretical. Mobus's framework is implemented in [BERT](https://github.com/halcyonic-systems/bert) (Bounded Entity Reasoning Toolkit), a working systems analysis application. The Lean proofs provide machine-checked foundations for the same concepts the tool implements visually.

## Venues

- **AITP 2026** (May): Extended abstract --- LLM-assisted formalization methodology, commuting triangle (draft: `docs/aitp-2026-abstract.md`)
- **ISSS 2026** (July): Presentation --- "What happens when you type-check Bunge" for systems science audience (draft: `docs/isss-2026-abstract.md`)
- **JOWO/FOIS 2026**: Workshop paper --- formal ontology methodology
- **Journal**: Full paper with BRA companion formalization

## Related

- [bitcoin-bra](../bitcoin-bra/) --- Bounded Resource Automata formalization (864 lines, Lean 4, targeting CPP 2027)
- [BERT](https://github.com/halcyonic-systems/bert) --- Systems analysis tool implementing Mobus's framework

## Documentation

- `docs/phase1-retrospective.md` --- structured analysis of where Lean forced choices on Bunge's text
- `docs/recursive-component-architecture.md` --- Phase 2 design decisions and mutual recursion problem
- `docs/aitp-2026-abstract.md` --- AITP extended abstract draft
- `docs/isss-2026-abstract.md` --- ISSS presentation abstract draft
- `docs/mobus-bunge-mathematical-reformulation-guide.md` --- exposition strategy for mathematician audience
- `docs/book-revisions.md` --- Mobus's revised 8-tuple definition
