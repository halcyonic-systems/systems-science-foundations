# Foundations for Mathematical Systems Science

Machine-verified formalization of seven systems science traditions in Lean 4, discovering their shared categorical structure. They build the future of systems theory. This audits its past.

**~4,700 lines | 34 files | zero `sorry`s | 7 traditions | K ≅ 2**

## The Result

Seven definitions of "system," developed independently across six decades (Klir 1964, Bunge 1979, Mesarovic 1975, Wymore 1993, Joslyn 1995, Mobus 2022, Myers 2023), all faithfully embed a single categorical structure: the walking arrow **2**. The irreducible content of "system" shared by every tradition is one morphism — *relations depend on things*. The common core is maximal: nothing larger embeds into all seven.

Three orientations emerge from the encoding:
- **Structural** (Klir, Bunge, Mobus): arrows converge inward toward components
- **Operational** (Mesarovic, Wymore, Myers): arrows radiate outward from state
- **Cybernetic** (Joslyn): arrows form a cycle — the only tradition with feedback in its shape category

## The Three Frameworks

Each tradition adds structure to the one before it. The formalization encodes all three faithfully and proves they compose.

| Tradition | Definition | What it captures |
|-----------|-----------|-----------------|
| **Klir** (1964) | `S = (T, R)` | Things and a relation. The simplest possible system. |
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
| 1 | **Common core theorem**: K ≅ **2** embeds faithfully into all 7 shape categories | Functor construction + pigeonhole maximality |
| 2 | **Commuting triangle**: Mobus → Bunge → Klir = Mobus → Klir | `rfl` (definitional equality) |
| 3 | **Bunge's 47-year error**: Def 1.6 (*Treatise*, Vol. 4, 1979) says "reflexive, asymmetric" — contradictory; correct: antisymmetric | Compiler rejection |
| 4 | **Statics-dynamics divide**: Mobus → Myers comparison functor — `update` has no preimage | Empty fiber |
| 5 | **Boundary completeness**: "all interaction mediated by boundary" is derived, not axiomatized | Structural consequence of bipartite constraint |
| 6 | **Bridge factorization**: `toBunge = toRichBunge ⋙ flatten` | Functor composition |
| 7 | **Joslyn incomparability**: cyclic shape generates infinite hom-sets; no faithful functor to any acyclic tradition | Open problem (traces, operads, double categories as candidates) |

## Known Limits

Structure formalizes cleanly. Dynamics and semantics don't. That's where the open problems live.

- **Transforms (T)**: encoded as `Unit`. No formal theory of what systems *do* — only what they *are*.
- **Rule/law distinction**: `ActsOn` is opaque — can't distinguish contingent from necessary relations.
- **Control**: active maintenance against disturbance requires temporal reasoning beyond the snapshot model.
- **Variety measures**: Joslyn's dimensional/cardinal variety has no formalization yet.

## Project Structure

```
Systems/
  Core/           Bunge ⟨C, E, S⟩ — things, bonds, subsystem order, emergence
  Mobus/          Mobus 8-tuple — flows, boundary, coherence constraints, bridge to Bunge
  Klir/           Klir S=(T,R) — common root, commuting triangle (rfl)
  Category/       Shape categories, comparison functors, common core theorem
docs/
  verso/          Verso interactive document (6 chapters)
  handout/        Standalone HTML+SVG companion
  publications/   AITP 2026, ISSS 2026 abstracts
  reference/      Technical docs, categorification roadmap
cql/              CQL categorical database schemas
```

## Building

Requires Lean 4 (v4.28.0) and Mathlib:

```bash
lake update   # fetch Mathlib (first time only)
lake build    # compile all modules — zero errors, zero sorrys
```

## Related

- [BERT](https://github.com/halcyonic-systems/bert) — Systems analysis tool implementing Mobus's framework. The coherence constraints Lean verifies (disjointness, bipartiteness, boundary completeness) are the grammar rules BERT's System Language compiles from.

## Methodology

Built in collaboration with Claude Code (Anthropic). Human editorial judgment and domain interpretation; LLM Lean syntax fluency and tactic generation; compiler final authority on every claim.

## License

MIT
