# Toward a Modular Categorical Definition of System

*How six decades of independent formalization converge on a common core — and how to extract it.*

*Companion to: systems-theory-definitions.md (formal comparative reference)*

---

## 1. The Problem

Building a formal system language — a specification language whose models are guaranteed to compose, whose ontological commitments are explicit, and whose compilation to different substrates (databases, simulations, neuromorphic hardware) is provably consistent — requires answering a question that systems science has spent sixty years debating: *what is a system?*

There is no consensus definition. There are six rigorous ones, each capturing a different level of abstraction:

| Theorist | Core formalism | Ontological stance |
|---|---|---|
| **Mesarović** (1964–75) | `S ⊆ ∏ V_i` — system as relation | Extensional |
| **Klir** (1969–85) | Epistemological hierarchy; `G = ⟨V, R⟩` | Epistemological |
| **Wymore** (1967–93) | 7-tuple `⟨T, X, Ω, Y, Q, δ, λ⟩` | Operational |
| **Bunge** (1979/2004) | CES triple `⟨C, E, S⟩` (def); CESM model `µ(σ) = ⟨C, E, S, M⟩` (representation) | Realist |
| **Mobus** (2015) | 6-tuple `{C, N, I, B, K, H}_l` | Operational/realist |
| **Joslyn** (1995) | Variety-theoretic; rule vs. law distinction | Synthetic |

These definitions are not competing so much as *layered*. They differ on at least six axes: substrate, time, environment, hierarchy, mechanism, and semantics. Bunge and Mobus converge independently on near-isomorphic ontologies — neither cites the other. Joslyn identifies a semiotic axis (rule vs. law) that no other definition addresses. The definitions partially agree and partially disagree, and the agreements and disagreements carry real ontological weight.

A formal system language must choose which commitments to make. The question is whether that choice can be principled — extracted from convergence rather than stipulated by fiat.

Category theory is the natural tool for this extraction. But the categorical and systems-theoretic communities are not connected, despite two earlier attempts to bridge them. This document maps the landscape, explains the disconnection, identifies what each prior attempt accomplished and missed, and defines the program that remains.

---

## 2. The Categorical Landscape: Five Threads

Applied category theory is not one field. It is at least five research programs. The gap between categorical mathematics and systems science becomes legible once you see which threads the relevant researchers live in.

| Thread | One-line definition | Canonical figures | Characteristic problem |
|---|---|---|---|
| **Enumerative** | Structures as functors from finite sets | Joyal, Bergeron, Labelle | Count structures; prove bijections |
| **Homotopical** | Smallness/generation conditions on model categories | Jeff Smith, Dugger, Lurie, Riehl | Present homotopy theory tractably |
| **Diagrammatic** | Categories from generators-and-relations; string diagrams | Burroni, Street, Power, Mimram | Rewriting; syntax of algebraic structures |
| **Structural** | Hypergraphs, sheaves, cell complexes for real-world systems | Joslyn, Robinson, Purvine, Spivak, Fong | Integrate heterogeneous data; compose open systems |
| **Semantic** | Categorical logic and universal algebra for computation and systems | Lawvere, Lambek, Goguen, Myers, Ghani | Compositional semantics of programs, proofs, and systems |

The classical systems science tradition (Mesarović, Klir, Wymore, Bunge, Mobus, Joslyn) lives in Thread 4 when it reaches for categorical tools at all. The foundational tools for defining "system" categorically live in Thread 5. The bridge was built twice — Goguen (1978), Takahara (1985) — and lost by both communities.

**Thread 1 (Enumerative).** Species, generating functions, bijective proofs. Irrelevant to systems modeling.

**Thread 2 (Homotopical).** Combinatorial model categories, ∞-categories. "Combinatorial" is a technical term of art about smallness, unrelated to Thread 1. Irrelevant to systems modeling.

**Thread 3 (Diagrammatic).** Polygraphs, computads, string diagram rewriting. Relevant to System Language as a *syntactic* framework — the System Language Specification is, in effect, a polygraph-style presentation with generators (components, interactions, levels) and relations (composition rules).

**Thread 4 (Structural).** Hypergraphs, cellular sheaves, structured cospans. Where the systems science tradition meets category theory — primarily through Joslyn and Purvine's work at PNNL.

**Thread 5 (Semantic).** Functorial semantics, lenses, doctrines, monads. Where the foundational question "what is a system categorically?" lives. Goguen's realization adjunction (1973), Takahara's symbolic functor method (1985), and Myers's compositionality theorem (2023) all live here.

---

## 3. The Prior Art

### Goguen (1972–1978)

Proved that *behavior is left adjoint to minimal realization* — a categorical universal property valid for discrete and linear machines. Published "A Categorical Approach to General Systems" (1978) with Ginali in a Klir-edited NATO volume, directly engaging the systems science community.

**Accomplished:** Categorical realization theory across system types.
**Did not accomplish:** Ontological treatment (Bunge), compositional framework (Myers), classification of system classes (Takahara).

### Takahara & Takai (1985)

Takahara — Mesarović's co-author — published "Category Theoretical Framework of General Systems" in the *International Journal of General Systems* (33 pages, citing Mesarović & Takahara 1975).

**The symbolic functor method:** A system class is a subcategory `D = [I, C; Φ_O, Φ_M]` of the functor category `C^I`, where `I` is a shape category (the "diagram" of a system type), `C` is a realization base (Set, Grp, R-Mod, Top, etc.), and `Φ_O`, `Φ_M` are categorical invariant properties. Systems are functors. Inter-class relationships are functors between subcategories.

**The four-step program:** (1) Categorize without assuming structure on C. (2) Derive realization-base-free properties. (3) Assume structural conditions (complete, algebraic, abelian). (4) Specialize to concrete C.

**Key results:** C-systems, C-morphic systems, and C-state representations as subcategories (Defs 2–3). Structure-forget functors between classes (Prop 6). State representability: every C-system in an abelian category has a C-state representation (Thm 1). Right adjoint `K: C-S → C-SR_f` with `H_2 ∘ K ≅ 1_{C-S}` (Thm 2). Counterexample: SGrp-systems need not have SGrp-state representations. Categories of C-time systems and C-complex systems with N-component subsystems.

**Accomplished:** Complete categorical classification of Mesarović-tradition system classes. Functorial relationships. Realization adjunction generalized. Forty years before Myers.

**Did not accomplish:** No ontological treatment (Bunge, Mobus). No epistemological treatment (Klir). No semiotic treatment (Joslyn). No compositionality theorem. Limited to static case. Not picked up by either community.

### Myers (2023)

*Categorical Systems Theory* — lenses, double categories, doctrines. Dedicated to Lawvere. Does not cite Mesarović, Wymore, Klir, Bunge, Mobus, Joslyn, Goguen (systems work), or Takahara.

**Accomplished:** The most technically powerful compositional framework for dynamical systems. System = lens in any cartesian category. General compositionality theorem: behaviors of composites decompose into component behaviors. Doctrine framework as meta-level for comparing systems theories.

**The compositionality theorem is the key deliverable.** If BERT's system coupling is an instance of lens composition — and the structural identification is already established in systems-theory-definitions.md — then the theorem gives a *formal guarantee* that behaviors of wired BERT systems decompose into behaviors of their components. This is not academic; this is what makes modular system design reliable. Myers built the engine. What he didn't do is point it at the classical landscape.

**Did not accomplish:** No engagement with any classical systems theory tradition. The preface explicitly routes around the definitional question. Myers's deterministic system is structurally identical to Wymore's at a single time step, arrived at independently. Wymore's coupling theory is the exact precursor to the compositionality theorem, but the lineage is invisible. No treatment of Goguen or Takahara.

---

## 4. Three Directions — and the One Nobody Has Taken

### Direction A: Lift one tradition (Goguen, Takahara)

Start with Mesarović. Categorify. Direction: set-theoretic definition → categorical framework.

**Gives you:** Rigorous categorical treatment of one tradition. Realization adjunctions. Classification of system classes.

**Misses:** The comparative question. Takahara never asks how Mesarović's categorification relates to what Wymore's or Bunge's would look like.

### Direction B: Build from categorical scratch (Myers, Topos/ACT)

Start with lenses. Prove compositionality. Introduce doctrines. Direction: categorical first principles → system definitions.

**Gives you:** The compositionality theorem. Interpretation across cartesian categories. The doctrine meta-level.

**Misses:** Everything the sixty-year tradition established. The philosophical rootlessness is structural, not incidental.

**The collaboration framing:** Myers built the compositional framework. Direction C brings the content — six decades of formal system definitions that his framework was designed for but hasn't been applied to. His compositionality theorem becomes *more* powerful when applied to richer doctrines. The question for joint work: does the compositionality theorem generalize to doctrines that carry Bunge's mechanism, Klir's levels, or Joslyn's semiotic typing? If yes, the theorem is stronger than proven. If no, the failure is diagnostic and publishable.

### Direction C: Comparative formalization of the plurality (the open direction)

Start from the *plurality* of definitions as the primary datum. Direction: comparative ontology → categorical formalization of the comparison → extraction of a minimal definition from convergence.

The question is not "how do we categorify systems theory?" (A) or "how do we build systems theory from lenses?" (B). The question is: **given six traditions that partially agree and partially disagree, what categorical apparatus makes the agreement and disagreement formally diagnosable — and what definition does the convergence extract?**

The tools it needs:
- Takahara's symbolic functor method, extended to shape categories derived from Bunge, Mobus, Klir, and Joslyn — not just Mesarović.
- Myers's doctrine framework, applied as *doctrine comparison* rather than doctrine construction.
- Structure-comparison functors between categorifications: where a functor exists, traditions agree; where it breaks, divergence is localized.
- Enrichment for Joslyn's semiotic axis.
- Myers's compositionality theorem, tested against each extended doctrine.

---

## 5. The Destination: A Modular Categorical Definition

Direction C is not purely comparative. The comparison *produces* something.

Construct shape categories `I_Mesarovic`, `I_Bunge`, `I_Mobus`, `I_Klir`, `I_Wymore`, `I_Joslyn`. Compute structure-comparison functors between them. Three things emerge:

**The common core.** The largest subcategory that embeds faithfully into *all* tradition-specific shape categories. This is the structure every tradition independently agrees on. Its robustness is demonstrated, not asserted: convergent formalization across independent traditions is the strongest possible evidence that the shared structure reflects something real about what systems are.

The Bunge/Mobus convergence is already evidence the core is nontrivial. Two thinkers who never read each other converged on most of the structure.

**The named extensions.** Each tradition adds structure beyond the core. These become formally identified *optional modules*:

| Module | Source | What it adds |
|---|---|---|
| **Mechanism** | Bunge (2004) | Mechanism `M(σ) = πs(σ) ⊆ π(σ)` — species-specific trajectory subset; part of the *model* µ(σ), not the system definition σ. Different categorical type from C/E/S (process-space vs. set-of-things) |
| **Epistemological levels** | Klir | Hierarchy of observational levels; likely a fibration |
| **Admissible inputs** | Wymore | Function space `Ω` as first-class component; trajectory structure |
| **Organization levels** | Mobus | Explicit levels-of-organization with inter-level relations |
| **Semiotic typing** | Joslyn | Rule/law enrichment on morphisms; contingent vs. necessary |
| **Composition** | Myers | Wiring diagrams, lens composition, compositionality theorem |

**The modular definition.** The minimal categorical system definition is: **the common core, equipped with a menu of named extensions that can be adjoined independently.** This is a *lattice* of definitions, ordered by extension, with the common core at the bottom and the fully-extended version (all modules) at the top. Each classical tradition occupies a specific position in this lattice.

The result is a categorical system definition that is:
- *Minimal:* the core includes nothing contested.
- *Extensible:* each tradition's additions are available as named modules.
- *Empirically grounded:* extracted from convergence, not stipulated.
- *Compositional:* the composition module (Myers) gives formal guarantees for modular design.
- *Machine-checkable:* the Lean 4 formalization targets become proof obligations.

Myers avoids the question of what a system *is*. This answers it — not by philosophical argument but by mathematical extraction from six decades of independent formalization.

---

## 6. Application: System Language v1.0

The modular categorical definition is directly applicable to BERT's System Language Specification.

**System Language as a doctrine.** The System Language Specification defines a specific shape category `I_SL` with specific object and morphism conditions. This is a doctrine in Myers's sense — a particular answer to what states are, what interfaces are, and how composition works. But it's a doctrine whose commitments are *traceable* to the classical landscape: the ontological core comes from the Bunge/Mobus convergence, the compositional structure comes from Myers, the semiotic typing (if included) comes from Joslyn.

**Compositionality as a design guarantee.** Myers's theorem, applied to `I_SL`, gives: when a user wires subsystems together in BERT, the behavior of the composite is computable from the component behaviors and the wiring pattern. This is the formal guarantee that makes modular system design reliable.

**Compilation as functorial semantics.** BERT's System Language compiles to multiple targets:
- TypeDB for storage (functor `I_SL → TypeDB`)
- Mesa for simulation (functor `I_SL → Mesa`)
- Neuromorphic substrates for execution (functor `I_SL → Spike`)

Each compilation is a functor from the same shape category to a different target. Consistency between compilations is a natural transformation. The compositionality theorem guarantees that the decomposition is preserved across targets.

**Soundness and completeness.** Soundness: every model of the System Language satisfies its constraints. Completeness: every intended system admits a model. Both are provable as theorems once the shape category and object conditions are specified in Lean 4.

**Which modules System Language includes** is a design decision, now made explicit:
- Common core: yes (every system language must include the convergent structure).
- Composition module: yes (BERT needs modular design; Myers's theorem applies).
- Mechanism module: likely yes (BERT implements Mobus's operational ontology, which includes mechanism).
- Level module: likely yes (BERT's multi-level modeling requires it).
- Semiotic module: open question (would distinguish rule-governed from law-governed subsystems — relevant for AI agent modeling, not yet implemented).
- Epistemological module: likely no for v1.0 (Klir's levels are about observational reconstruction, not system specification).
- Admissible-input module: likely no for v1.0 (Wymore's trajectory structure adds complexity without clear payoff for BERT's current use cases).

---

## 7. Where Specific Figures Fit

| Figure | Primary thread | Secondary | Note |
|---|---|---|---|
| **Goguen** | Semantic | Diagrammatic | Realization adjunction (1973); categorical GST in Klir's NATO volume (1978) |
| **Takahara / Takai** | Semantic | — | Symbolic functor method (1985); Mesarović's co-author |
| **Joyal** | Enumerative | Semantic | Species; also foundational to string diagrams |
| **Lurie** | Homotopical | — | *Higher Topos Theory* |
| **Spivak** | Structural | Semantic | Bridges applied CT and compositional programming |
| **Fong** | Structural | Semantic | Decorated cospans, backprop as functor |
| **Joslyn** | Structural | — | Klir-school; reached CT through hypergraph analytics |
| **Robinson** | Structural | — | Cellular sheaves for heterogeneous data |
| **Myers** | Semantic | Structural | Compositionality theorem; doctrine framework; does not engage classical GST |
| **Lawvere** | Semantic | — | Functorial semantics; foundation of Thread 5 |
| **Lambek** | Semantic | Diagrammatic | Deductive systems as categories |
| **Symbolica (2022–24)** | Diagrammatic | Structural | Hypergraph rewriting phase |
| **Symbolica (2024–)** | Semantic | — | CDL → types / program synthesis |
| **Topos Institute** | Structural | Semantic | Institutional home for both threads |

---

## 8. Where Halcyonic Systems Fits

**Halcyonic is a Direction C project with a Direction B collaborator.**

The starting point is the *plurality* of system definitions as the primary datum — six traditions that partially agree and partially disagree. The deliverable is not a survey but a *modular categorical system definition* extracted from convergence, implemented in a formal system language (BERT's System Language), with compositionality guarantees from Myers's theorem.

**What's already done:**
- The comparative reference (systems-theory-definitions.md) mapping all seven definitions against each other, with formal mappings, verification status, and Lean 4 formalization targets.
- BERT's implementation of Mobus's ontology in Rust/Tauri/Bevy.
- The Bunge/Mobus convergence observation (independent formalization, no citation).
- The System Language Specification v0.1.

**What Takahara enables:**
- Shape categories `I` for each tradition using the symbolic functor method.
- Structure-comparison functors between categorifications.
- Formal extraction of the common core.

**What Myers enables:**
- The compositionality theorem applied to System Language's specific doctrine.
- Formal guarantee that modular BERT system design is reliable.
- Compilation as functorial semantics with cross-target consistency.

**The novel contributions:**
- Multiple shape categories for multiple traditions (extends Takahara).
- Structure-comparison functors between them (new).
- Common core extraction (new).
- Named extension modules (new).
- Joslyn's semiotic axis as enrichment (new).
- System Language v1.0 as a specific position in the definition lattice (new).

---

## 9. Next Steps

1. **Construct `I_Bunge` and `I_Mobus` as shape categories using Takahara's method.** Build the structure-comparison functor. Catalogue the divergences. This is the proof-of-concept and a publishable result independent of everything else.

2. **Verify that BERT's system coupling is an instance of Myers's lens composition.** If confirmed, the compositionality theorem applies to BERT immediately.

3. **Formalize the common core in Lean 4.** The Lean targets in systems-theory-definitions.md are the proof obligations.

4. **Write the System Language Specification v1.0** as a specific doctrine: shape category, object conditions, morphism conditions, with explicit module selections and compositionality theorem.

5. **Reach out to Myers** with the Bunge/Mobus shape-category construction. The pitch: "You proved compositionality for the parameter-setting doctrine. Here are five other doctrines from the classical landscape. Does your theorem generalize?" That's a joint paper whether the answer is yes or no.

6. **Investigate Goguen→Myers connection.** Is the system-as-lens identification a rephrasing of Goguen's behavior-realization adjunction?

---

## 10. Further Reading, by Thread

**Thread 1.** Bergeron–Labelle–Leroux, *Combinatorial Species and Tree-like Structures*.

**Thread 2.** Lurie, *Higher Topos Theory*. Riehl, *Categorical Homotopy Theory*.

**Thread 3.** Mimram's lecture notes on rewriting in monoidal categories. Lafont on interaction combinators.

**Thread 4.** Spivak, *Category Theory for the Sciences*. Fong–Spivak, *Seven Sketches in Compositionality*. Purvine–Joslyn–Robinson (2016). Curry's thesis.

**Thread 5.** Goguen, *Realization is Universal* (1973). Ginali–Goguen (1978). Takahara & Takai (1985). Lambek–Scott. Moggi. Myers (2023). Gavranović et al. (2024). Joslyn (1995).

---

## Appendix A — How the AI Overview Went Wrong

The original AI Overview that prompted this document lumped Threads 1, 2, and 4 under "combinatorial category theory" and contrasted them with a caricature of Threads 3 and 5 labeled "set-theoretic/algebraic." This is wrong on three counts:

1. *Combinatorial* means different things in Threads 1 and 2 and is a stretch for Thread 4.
2. Thread 5 (Lambek, Lawvere) is foundational mainstream category theory, not an exotic alternative school.
3. The set-theory-vs-category-theory axis cuts *across* all five threads.

## Appendix B — Symbolica AI: Thread Placement

Symbolica went through three phases: hypergraph rewriting (Thread 3, 2022–early 2024), Categorical Deep Learning via Gavranović et al.'s ICML 2024 position paper (Thread 5), and a post-CDL product pivot to agent-building and program synthesis (Thread 5, current). The key CDL researchers were fired shortly after the Series A. The Gavranović / Coend line is the more trustworthy continuation of the CDL program. Relevant as a Thread 5 reference, not a model to emulate.

## Appendix C — Cliff Joslyn: Thread Placement

Joslyn sits in Thread 4 (Structural), rooted in Klir-school systems science and cybernetics (PhD under George Klir, Binghamton, 1994). His native mathematical languages are generalized information theory, possibility theory, and order/lattice theory. Category theory entered his toolkit through hypergraph analytics and sheaf-theoretic sensor integration at PNNL (with Purvine and Robinson). His 2018 talk "Seeking a categorical theory of systems through the category of hypergraphs" at the NIST Applied Category Theory meeting is the clearest statement of his categorical direction. Closest neighbors: Robinson, Curry, Ghrist (cellular sheaves), Spivak and Fong (compositional systems).
