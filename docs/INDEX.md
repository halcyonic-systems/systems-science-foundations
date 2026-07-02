# Documentation Index

*Reading order for the systems-science-foundations project*

## Start Here

| Document | What it tells you |
|----------|------------------|
| [README.md](../README.md) | Project overview, headline findings, how to build |
| [CLAUDE.md](../CLAUDE.md) | Technical structure, conventions, dependency graph |

## The Two Programs

This project has two research programs. The first (categorification) is substantially complete. The second (axiomatization) is active.

### Program 1: Common Core Theorem (K ≅ 2)

Seven systems traditions encoded as shape categories, compared via functors, unified by a common core.

| Document | What it covers |
|----------|---------------|
| [common-core-theorem.md](reference/common-core-theorem.md) | The main result: K ≅ **2** embeds faithfully into all 7 traditions |
| [categorification-roadmap.md](reference/categorification-roadmap.md) | Phase-by-phase plan for the categorical infrastructure |
| [three-layer-architecture.md](reference/three-layer-architecture.md) | How Klir, Bunge, and Mobus layer on each other |
| [mobus-bunge-system-definitions-reference.md](reference/mobus-bunge-system-definitions-reference.md) | Side-by-side definition comparison |
| [mobus-bunge-mathematical-reformulation-guide.md](reference/mobus-bunge-mathematical-reformulation-guide.md) | How Mobus's prose translates to Bunge's set theory |
| [systems-theory-definitions.md](reference/systems-theory-definitions.md) | Definitions from all traditions with source citations |
| [structure-family-context.md](reference/structure-family-context.md) | The RichConcreteSystem experiment (not imported) |
| [recursive-component-architecture.md](reference/recursive-component-architecture.md) | Design decisions for RecursiveSystem vs RecursiveComponent |
| [spivak-adaptive-arrangements.md](reference/spivak-adaptive-arrangements.md) | Spivak 2026 as candidate entry #8: "system = 0-ary morphism," Def 5.3.2 unpacked, formalization targets |

### Program 2: Principles Axiomatization (12 → ≤11)

Formalizing Mobus's 12 principles to test which are independent axioms and which are theorems.

| Document | What it covers |
|----------|---------------|
| [principles-formalization-companion.md](reference/principles-formalization-companion.md) | **The primary deliverable**: axiom table, findings, practical implications |
| [principles-formalization-roadmap.md](reference/principles-formalization-roadmap.md) | Technical assessment of all 12 principles, sequencing, proof scaffolds |
| [simon-argument-formalized.md](reference/simon-argument-formalized.md) | Simon's "Architecture of Complexity" decomposed under proof — the full chain |
| [governance-mathematical-foundations.md](reference/governance-mathematical-foundations.md) | Research survey: lenses, traces, polynomials as governance primitives — Zotero gaps and recommendations |

### Collaboration and External

| Document | What it covers |
|----------|---------------|
| [joslyn-collaboration-artifact.md](reference/joslyn-collaboration-artifact.md) | Joslyn's cybernetic tradition and collaboration notes |
| [joslyn-feedback-mapping.md](reference/joslyn-feedback-mapping.md) | Mapping Joslyn's feedback structure to the shape category |
| [for-cliff-structure-of-S.md](reference/for-cliff-structure-of-S.md) | Structure analysis prepared for Cliff (advisor) |
| [toward_a_modular_categorical_definition_of_system.md](reference/toward_a_modular_categorical_definition_of_system.md) | Early paper draft on modular categorical systems |
| [formalization-practice-references.md](reference/formalization-practice-references.md) | LAMP (agentic proving + ontology-tool plan) and Scott 1972 (engineering patterns, genre precedent) |

### Publications

| Document | Venue |
|----------|-------|
| [aitp-2026-abstract.md](publications/aitp-2026-abstract.md) | AITP 2026 — LLM-assisted formalization |
| [isss-2026-abstract.md](publications/isss-2026-abstract.md) | ISSS 2026 — "What happens when you type-check Bunge" |

## The Lean Code

See [CLAUDE.md](../CLAUDE.md) for the full dependency graph. Quick orientation:

```
Systems/
  Core/        Phase 1: Bunge CES + Principles formalization
               (Thing → Bond → System → Level → Assembly → Selection → State
                → Systemness → Complexity → Dynamics → Governance)
  Mobus/       Phase 2: 8-tuple + Composition
  Klir/        Phase 3: Common root S=(T,R)
  Category/    Shape categories, comparison functors, K ≅ 2
  Bunge/       Experimental (StructureFamily, not imported)
  Examples/    Thermostat
```

## The CQL Layer

Categorical database schemas bridging Lean proofs to real-world data. See `cql/` directory. Run with `cql -i cql/test_instance.cql`.
