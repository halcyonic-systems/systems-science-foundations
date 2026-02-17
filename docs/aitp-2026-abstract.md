# LLM-Assisted Formalization of Systems Ontology: From Cryptocurrency to Philosophy in 1,746 Lines of Lean 4

**Venue**: AITP 2026 — AI for Theorem Proving
**Format**: Extended abstract (2 pages excluding references, easychair.cls)
**Status**: Draft for formatting

---

## Abstract

We report on LLM-assisted formalization of two independently developed systems ontologies in Lean 4: Bunge's CES triple (1979) and Mobus's 8-tuple (2022). The formalization comprises 1,746 lines of machine-verified mathematics with zero `sorry`s. A companion project formalizes bounded-resource automata for cryptocurrency analysis (882 lines, also zero `sorry`s). Both were produced using the same methodology: a domain expert provides editorial judgment and conceptual direction while an LLM (Claude) generates Lean code against the Mathlib library and the compiler verifies. We describe three categories of findings that formalization surfaced about philosophical texts in continuous print since 1979, and report on the discovery that two frameworks developed 43 years apart by authors who never reference each other are formally compatible.

## 1. Introduction

Formal verification of philosophical ontology is unusual territory for a proof assistant. Bunge's *Treatise on Basic Philosophy* (1979) and Mobus's *Understanding Systems* (2022) each propose mathematical definitions for "system" — but their mathematics is embedded in prose, with notation that is suggestive rather than precise. Neither author uses mechanized proof. Neither references the other.

We formalized both. Phase 1 encodes Bunge's Chapter 1 — the Composition–Environment–Structure (CES) triple, subsystem partial order, assembly and emergence, selective action, level structure, and state functions — across 7 Lean modules (864 lines, 74 declarations). Phase 2 encodes Mobus's revised 8-tuple — components, flow networks, environment with parametric milieu, boundary with interfaces, transforms, history, and time scale — across 6 modules (882 lines, 46 declarations). A bridge theorem proves that every well-formed Mobus system projects to a valid Bunge CES triple. The entire codebase builds against Lean 4 / Mathlib (v4.28.0) with zero `sorry`s.

The methodology is what Tagliabue (2025) calls "vibe proving": the human steers; the LLM writes Lean; the kernel checks. Our experience confirms and extends his observations. The LLM contribution is fluency with Lean syntax, Mathlib API navigation, and tactic proof generation. The human contribution — which no current LLM can replicate — is knowing *what* to formalize, making interpretation choices when the source text is ambiguous, and recognizing when the LLM's output is type-correct but conceptually wrong.

A companion formalization of Bounded Resource Automata (BRA) for cryptocurrency modeling (882 lines, targeting CPP 2027) was produced using the same workflow, suggesting the methodology generalizes across domains.

## 2. What the Compiler Found

Formalizing philosophical prose in a dependently typed language forces every ambiguity into the open. We categorize our findings into three groups.

**Error detection.** Bunge (Def 1.6) describes the subsystem relation as "reflexive, asymmetric, and transitive." This is mathematically contradictory — a relation cannot be both reflexive ($a \leq a$) and asymmetric ($a \leq b \Rightarrow \neg(b \leq a)$). Lean refuses to typecheck both properties simultaneously. He clearly means *antisymmetric* ($a \leq b \wedge b \leq a \Rightarrow a = b$), i.e., a partial order. The formalization proves reflexivity, transitivity, and antisymmetry — correcting an error that has been in print since 1979. This is a case where the proof assistant catches what 47 years of human reading did not.

**Under-specification revealed.** Several definitions that appear precise in prose turn out under-determined when typed. Bunge *defines* environment as the set of things bonded to components but not in the composition — a derived set. Our `ConcreteSystem` declares `environment : Set α` as a free parameter with no constraint linking it to the `ActsOn` relation, because enforcing derivedness would require quantifying over all possible bonds. Bunge's Corollary 1.1 ("the universe is the only closed system") is proved as a tautology: `σ.isClosed ↔ σ.environment = ∅`, which is the *definition* of `isClosed`. The substantive uniqueness claim requires an external axiom (Vol. 3, Postulate 5.10) — a cross-volume dependency invisible in the prose numbering but structurally undeniable in the type system.

**Independent convergence discovered.** The headline result: Bunge's CES triple (philosophical ontology, 1979) and Mobus's 8-tuple (systems science, 2022) are formally compatible despite independent development. Our bridge theorem `toBunge` maps every Mobus system to a valid Bunge system. The map sends components to composition (exact), environment objects to environment (milieu discarded), and total relation to structure (capacity labels discarded). Three field-characterization theorems prove by `rfl` — definitional equality, requiring no proof search — that the preserved fields align perfectly. The subsystem partial order transfers by direct field mapping. Six categories of information loss (milieu, capacity, boundary properties, transforms, history, time scale) precisely characterize where the engineering tradition captured structure that the philosophical tradition did not require. These `rfl` proofs are not trivially expected — they are empirical findings that two researchers working in different traditions, with different notation, terminology, and motivating examples, happened to decompose the concept of "system" in structurally identical ways.

## 3. Methodology Observations

Our workflow over the two projects (approximately 100 human-LLM interaction rounds across both formalizations) yields several observations for the AITP community:

**The LLM is a fluent but uncritical formalizer.** Claude generates syntactically valid Lean and navigates Mathlib competently. It rarely produces kernel errors on the first attempt for definitions and straightforward lemmas. But it does not *understand* what it formalizes. When Bunge's prose is ambiguous, the LLM picks a reading — often the simplest one — without flagging the choice. The human must catch these and decide whether the simplification is acceptable or distorting.

**Build-test-fix cycles are fast.** Most modules compiled on the first or second attempt. When they didn't, the failures were informative: a pair-equality projection that required explicit rewriting, a missing disjointness hypothesis, a proof term that needed a `rw` step to transfer membership across an equality. These are exactly the kind of errors that LLMs can fix quickly once told *what* went wrong.

**The hard problems are not proof search.** No individual proof required more than a few tactic steps. The hard problems were representational: should `ActsOn` reference `HasStateSpace`? Should `environment` be a field or derived from `structure'`? Should we use `Set` or `Finset`? These decisions propagate through the entire codebase and are irreversible without refactoring. They require understanding the source material, not Lean expertise.

**Operational grounding.** The formalized ontology is not academic exercise. Mobus's framework is implemented in BERT (Bounded Entity Reasoning Toolkit, github.com/halcyonic-systems/bert), a working systems analysis application. The Lean proofs provide machine-checked foundations for the same concepts the tool implements visually. This connection — formal ontology grounding operational software — is enabled by the low marginal cost of LLM-assisted formalization.

## References

- Bunge, M. (1979). *Treatise on Basic Philosophy*, Vol. 4: *A World of Systems*. Reidel.
- Mobus, G.E. (2022). *Understanding Systems: A Grand Challenge for 21st-Century Engineering*. Springer.
- Mobus, G.E. (2024). Book revisions to the 8-tuple system definition. Personal communication.
- Tagliabue, F. (2025). Vibe proving: LLM-assisted formal verification. *Preprint*.
- [Author] (in preparation). Bounded Resource Automata: A Lean 4 formalization of cryptocurrency state machines. Targeting CPP 2027.
- The mathlib Community (2020). The Lean mathematical library. *CPP 2020*.
