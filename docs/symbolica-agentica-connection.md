# Symbolica / Agentica — Potential Runtime Target for Categorical Systems Infrastructure

*Logged 2026-03-27*

## What Symbolica Is

Category theory-native AI research lab. Their reasoning harness powered SOTA on ARC-AGI benchmarks. Agentica is their agent SDK: type-safe, stateful Python runtime where you pass live objects/functions to LLM agents with enforced contracts.

- Product: https://www.symbolica.ai
- SDK docs: https://docs.symbolica.ai
- Python SDK: https://github.com/symbolica-ai/agentica-python-sdk

## Why This Matters for Systems Ontology

Symbolica uses category theory for AI reasoning. We use it for systems formalization. The mathematical foundations overlap significantly. Three specific connection points:

### 1. CQL ↔ Agentica typed agents

CQL models schemas as small categories, instances as functors `C → Set`, and migrations as Sigma/Delta/Pi operations. Our CESM schema + GovGraph mapping is a functor between two categorical schemas with semantic interpretation.

Agentica's "type-safe agents" enforce compositional contracts at runtime — functions become typed morphisms, agent composition respects types. The gap between CQL's categorical data migrations and Agentica's typed agent composition is structurally analogous:

| CQL | Agentica |
|---|---|
| Schema = small category | Agent toolset = typed interface |
| Instance = functor C → Set | Agent state = runtime objects |
| Migration = Sigma/Delta pushforward | Agent composition = typed function composition |
| Constraint = path equation | Contract = type annotation enforcement |

**Question worth investigating**: Can CQL schemas serve as the type system for Agentica agents? I.e., could a CESM-typed agent enforce that its outputs satisfy categorical constraints derived from the formal proofs?

### 2. BERT validation pipeline as functorial agent chain

The BERT development roadmap (Facets Phase C/D) envisions:
```
BERT JSON → RDF ontology → coherence check → validated model
```

Each step is a morphism. The coherence check applies the 5 constraints from Tuple.lean. If this pipeline were implemented as Agentica agents, each step would be a typed agent with enforced input/output contracts — and the composition would be functorial by construction.

This is more principled than the current approach (LlamaIndex query engine → JSON parse → hope it's valid).

### 3. Categorification Phase 3+ alignment

The categorification roadmap's speculative phases include:
- 3.1: Mobus boundary as polynomial functor (Spivak)
- 3.2: System assembly as operad algebra
- 3.3: Nester-Lambert bridge (topos + SMC)
- 3.4: Joslyn semantic control systems

If Symbolica exposes categorical primitives in their SDK (functorial composition, natural transformations as agent protocol morphisms), these speculative phases could have a runtime target — not just Lean proofs but executable categorical infrastructure.

## Status: Watch

Not ready to adopt. Facets works without it. Agentica is brand new (early adoption risk). But the mathematical alignment is real and worth tracking. Revisit when:

- Phase B.6 (direct Claude synthesis) removes LlamaIndex dependency — cleaner integration surface
- Phase C (ontology validation) needs typed multi-agent pipeline — Agentica's natural use case
- Symbolica publishes more on their CT foundations — check if functorial composition is exposed in the SDK

## Not a Dependency, Potentially a Collaboration

The deeper opportunity is research alignment, not tool adoption. Symbolica is building CT-native AI infrastructure. We're building CT-verified systems ontology. A joint demo — Agentica agents reasoning through Lean-verified categorical constraints — would be a compelling artifact for ISSS/AITP audiences.
