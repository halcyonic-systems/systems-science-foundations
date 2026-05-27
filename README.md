# Foundations for Mathematical Systems Science

Machine-verified formalization of seven systems science traditions in Lean 4, discovering their shared categorical structure. They build the future of systems theory. This audits its past.

**~6,265 lines | 39 files | zero `sorry`s | 7 traditions | K ≅ 2 | 12 → ≤11 principles**

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
| 8 | **Unconditional composition**: system composition is valid at both CES and 8-tuple levels without interaction hypotheses | Coherence proofs don't reference cross-system data |
| 9 | **Complexity is not an axiom**: structural measures derive from Systemness + Hierarchy + Networks | Complexity.lean compiles with only Core imports |
| 10 | **Simon's named gap**: near-decomposability → time-scale separation requires an unstated StrictAnti assumption | Conditional theorem isolates the bridge |
| 11 | **Timescale decomposition**: coupled dynamics decomposes into fast (within-module) and slow (between-module) around equilibria | Fast equilibria = product equilibria (by rfl) |

## Principles Axiomatization (active)

Mobus lists 12 principles of systems science. We're testing which are independent axioms and which are theorems — the first systematic axiomatization attempt.

**Status**: 6 principles resolved. Complexity (#5) is not an axiom — it derives from Systemness + Hierarchy + Networks. Governance (#8) is an axiom — the set point is genuinely new structure. The 12 reduce to ≤11.

| # | Principle | Status |
|---|-----------|--------|
| 1 | Systemness | **Axiom** — composition closure unconditional at CES and 8-tuple levels |
| 2 | Hierarchy | **Axiom** — Simon's implicit assumption named (StrictAnti bridge to Dynamics) |
| 3 | Networks | **Axiom** — complete |
| 4 | Dynamics | **Axiom** — DynamicSystem, coupled dynamics, equilibrium, Flow, timescale decomposition |
| 5 | Complexity | **Theorem** — structural measures derive from #1+#2+#3. First reduction. |
| 8 | Governance | **Axiom** — Homeostat, GovernanceSubsystem, HCGS; set point is new structure not in Dynamics |

Key findings: unconditional composition (CES and 8-tuple), Simon's named gap, forced environment formula, diversity from interaction profiles. See `docs/reference/principles-formalization-companion.md` for the full axiom table and findings.

## Known Limits

- **Quantitative dynamics**: multi-timescale convergence needs metric space infrastructure (structural skeleton is complete).
- **Rule/law distinction**: `ActsOn` is opaque — can't distinguish contingent from necessary relations.
- **Control**: Governance (#8) is formalized as an axiom. Connecting to ShapeJoslyn categorically (the cycle IS the feedback loop) is future work.
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
  reference/      15 technical docs (companion, roadmaps, Simon analysis)
  publications/   AITP 2026, ISSS 2026 abstracts
  verso/          Verso interactive document (6 chapters)
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
