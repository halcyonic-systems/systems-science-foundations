# LLM-Assisted Formalization of Systems Ontology: Verified Convergence of Independent Frameworks in Lean 4

**Venue**: AITP 2026 — AI for Theorem Proving
**Format**: Extended abstract (2 pages excluding references, easychair.cls)
**Status**: Draft for formatting

---

## Abstract

We report on LLM-assisted formalization of three independently developed systems ontologies in Lean 4, producing a verified commuting triangle: Klir's `S = (T, R)` (1969/2001), Bunge's CES triple (1979), and Mobus's 8-tuple (2022). The systems ontology formalization comprises ~2,930 lines across 20 Lean modules with zero `sorry`s, including a categorification layer that packages subsystem orderings, flattening, and the Mobus-Bunge bridge as Mathlib functors. A companion project formalizes bounded-resource automata for cryptocurrency analysis (~1,080 lines across 11 files, also sorry-free, targeting CPP 2027); its collapse map from Bitcoin's UTXO model to Ethereum's account model is now a proper Mathlib functor (`collapseFunctor : BtcState ⥤ EthState`) with `EssSurj` (essentially surjective) and `¬ Faithful` proved --- the latter a new result that the pre-categorical formalization could not state. Both projects were produced using the same methodology: a domain expert provides editorial judgment and conceptual direction while an LLM (Claude) generates Lean code against the Mathlib library and the compiler verifies. We describe findings that formalization surfaced about philosophical texts in continuous print since 1979, and prove that three frameworks spanning 50 years of independent development form a commuting diagram.

## 1. Introduction

Formal verification of philosophical ontology is unusual territory for a proof assistant. Klir's *Facets of Systems Science* (2001), Bunge's *Treatise on Basic Philosophy* (1979), and Mobus's *Systems Science: Theory, Analysis, Modeling, and Design* (2022) each propose mathematical definitions for "system" --- but their mathematics is embedded in prose, with notation that is suggestive rather than precise. None uses mechanized proof. Crucially, while both Bunge and Mobus cite Klir independently, *neither references the other*. They developed their elaborations of Klir's framework without mutual knowledge.

To our knowledge, this is the first proof-assistant formalization of systems science foundations. Adjacent communities --- applied category theory (Spivak, Fong), formal ontology (Guizzardi's UFO, DOLCE/BFO), and systems engineering (INCOSE ontology stacks) --- work on related structures but without machine verification. Prior attempts to check foundational ontologies with automated theorem provers (Garbacz 2022, using TPTP on DOLCE and BFO) report scalability failures. The gap at the intersection of *systems science*, *proof assistants*, and *cross-framework comparison* appears to be unoccupied.

We formalized all three. The Bunge formalization (Phase 1) encodes Chapter 1 of Vol. 4 --- the Composition--Environment--Structure (CES) triple, subsystem partial order, assembly and emergence, selective action, level structure, and state functions --- across 9 Lean modules (858 lines). The Mobus formalization (Phase 2) encodes the revised 8-tuple --- components, flow networks, environment with parametric milieu, boundary with interfaces, transforms, history, and time scale --- across 6 modules (886 lines). The Klir formalization (Phase 3) encodes `S = (T, R)` and proves the commuting triangle in 1 module (146 lines). A StructureFamily module (475 lines) verifies that the flat structure encoding is a faithful quotient of the richer family representation. A categorification layer (4 modules, 563 lines) packages subsystem orderings as thin categories, flattening as a Mathlib functor, and the Mobus-Bunge bridge as a functor factorization (`bridge_factors_functor`). The entire codebase builds against Lean 4 / Mathlib (v4.28.0) with zero `sorry`s.

The methodology is what Tagliabue (2025) calls "vibe proving": the human steers; the LLM writes Lean; the kernel checks. The LLM contribution is fluency with Lean syntax, Mathlib API navigation, and tactic proof generation. The human contribution --- which no current LLM can replicate --- is knowing *what* to formalize, making interpretation choices when the source text is ambiguous, and recognizing when the LLM's output is type-correct but conceptually wrong.

## 2. The Commuting Triangle

Klir (Eq. 1.1) defines a system as a pair `S = (T, R)`: a set of things $T$ and a relation $R$ on $T$. This is the mathematical common ancestor:

- **Bunge** (1979) cites Klir \& Valach (1967) and Klir \& Rogers (1977). He added environment as a third first-class component: $\langle C, E, S \rangle$. Philosophical ontology: *what is a system?*

- **Mobus** (2022) cites Klir (2001) explicitly as inspiration (Ch. 4, p. 14). He elaborated $R$ into typed flow networks with capacity labels, added boundary, interfaces, transforms, history, and time scale: the 8-tuple $\langle C, N, E, G, B, T, H, \Delta t \rangle$. Engineering methodology: *how do you describe a system?*

The Lean formalization proves three projection maps and one commutativity result:

```lean
def ConcreteSystem.toKlir (s : ConcreteSystem α) : KlirSystem α :=
  ⟨s.composition, s.structure'⟩

def MobusSystem.toKlir (sys : MobusSystem α κ μ π τ η δ) : KlirSystem α :=
  ⟨sys.components, sys.totalRelation⟩

theorem triangle_commutes (sys : MobusSystem α κ μ π τ η δ) (hf hg) :
    (sys.toBunge hf hg).toKlir = sys.toKlir := rfl
```

The `rfl` proof is the result: both paths through the diagram --- Mobus $\to$ Bunge $\to$ Klir and Mobus $\to$ Klir --- produce *definitionally identical* output. The type-checker confirms this without proof search. The definitional equality traces to both Bunge and Mobus inheriting $T$ as `Set α` and $R$ as `Set (α × α)` from Klir without changing the mathematical type.

The six information loss categories in the Mobus $\to$ Bunge projection (milieu, capacity, boundary properties, transforms, history, time scale) correspond precisely to where the engineering tradition elaborated Klir's framework in directions the philosophical tradition did not require.

## 3. What the Compiler Found

**Error detection.** Bunge (Def 1.6) describes the subsystem relation as "reflexive, asymmetric, and transitive." This is contradictory --- reflexive and asymmetric are incompatible. He means *antisymmetric*, i.e., a partial order. Lean refuses to typecheck both properties simultaneously, catching an error in print since 1979.

**Cross-volume dependencies.** Corollary 1.1 ("the universe is the only closed system") is proved as a tautology: `σ.isClosed ↔ σ.environment = ∅` is the *definition* of `isClosed`. The substantive claim requires Postulate 5.10 from Vol. 3 --- a dependency invisible in the prose numbering but structurally undeniable in the type system.

**Under-specification.** Bunge *defines* environment as derived from the bond relation, but the formalization declares it as a free parameter --- enforcing derivedness would require quantifying over all possible bonds. His `ActsOn` is defined via state-space trajectories, but reduces to an opaque binary relation because the state-space semantics add no structural content at this abstraction level.

**Clean compositions.** Selection composition (Theorem 1.2) proves by `rfl` --- the definitions align perfectly. Emergence decomposes into set operations via `simp`. Bipartite external flows imply boundary completeness as a free structural consequence rather than an axiom.

**Faithful encoding.** The flat relation encoding used throughout is verified to be a faithful quotient of the richer family representation: flattening commutes with internal/external decomposition (`flatten_internal_commutes`, `flatten_external_commutes`).

**Categorical upgrade.** The companion BRA project now defines Bitcoin's UTXO model and Ethereum's account model as Mathlib categories and constructs a proper functor between them (`collapseFunctor : BtcState ⥤ EthState`). The functor is essentially surjective (`EssSurj`) but not faithful (`collapse_not_faithful_cat`) --- two distinct UTXO transaction traces can produce the same balance-level transition. This non-faithfulness result is genuinely new: it requires categorical vocabulary (injectivity on hom-sets) that the pre-categorical formalization could not express.

## 4. Methodology Observations

**The LLM is fluent but uncritical.** Claude generates valid Lean and navigates Mathlib competently. But when source prose is ambiguous, it picks a reading without flagging the choice. The human must catch distorting simplifications.

**The hard problems are representational, not proof search.** No proof required more than a few tactic steps. The hard decisions were: should `ActsOn` reference `HasStateSpace`? Should `environment` be a field or derived from `structure'`? Should we use `Set` or `Finset`? These propagate through the codebase and require understanding the source material, not Lean expertise.

**Operational grounding.** The formalized ontology is not academic exercise. Mobus's framework is implemented in BERT (Bounded Entity Reasoning Toolkit, github.com/halcyonic-systems/bert), a working systems analysis tool. The Lean proofs provide machine-checked foundations for the same concepts the tool implements visually --- formal ontology grounding operational software, enabled by the low marginal cost of LLM-assisted formalization.

## References

- Bunge, M. (1979). *Treatise on Basic Philosophy*, Vol. 4: *A World of Systems*. Reidel.
- Klir, G.J. (2001). *Facets of Systems Science*. 2nd ed. Springer.
- Mobus, G.E. (2022). *Systems Science: Theory, Analysis, Modeling, and Design*. Springer.
- Mobus, G.E. (2024). Book revisions to the 8-tuple system definition. Personal communication.
- Tagliabue, J. (2025). Understanding vibe proving. *Towards Data Science*.
- [Author] (in preparation). Bounded Resource Automata: A Lean 4 formalization of cryptocurrency state machines (~1,080 lines, 11 files, zero sorry). Targeting CPP 2027.
- The mathlib Community (2020). The Lean mathematical library. *CPP 2020*.
- de Moura, L. & Ullrich, S. (2021). The Lean 4 theorem prover and programming language. *CADE-28*.
