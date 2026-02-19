# Building Story: From a Flawed Paper to ~4,010 Lines of Certified Mathematics

*A 48-hour arc of curiosity, critique, construction, discovery, and integration — how a systems science PhD student who had never written a line of Lean 4 ended up with two publication-ready formalizations, a commuting triangle connecting three independent ontologies, and a correction to a foundational text that had stood for 47 years.*

*February 16–18, 2026*

---

## 1. The Spark

It began with a 222-page paper claiming that Bitcoin reveals fundamental physics.

The paper was ambitious. It proposed that cryptocurrency protocols encode deep physical principles — that the structure of blockchain ledgers somehow illuminates the structure of reality. Reading it carefully, Claude (the AI) identified the core problem: an ontological category error at Layer 3 of the paper's framework. Protocol properties were being treated as physical properties. The mathematical observations underneath were real — Bitcoin's UTXO set genuinely has interesting computational structure — but the physics framing was wrong.

The pivotal moment came from a single question:

> *"What completely different direction would you take this paper for someone interested in genuinely novel rigorous systems theory? Grounded in set, graph, category theory?"*

Not "how do I critique this paper?" but "what's the REAL mathematics here?"

That question changed everything. Instead of a critique, it became a construction.

---

## 2. The Proposal

The answer to the question was a framework called Bounded-Resource Automata (BRA). The core insight: Bitcoin's UTXO model defines a novel computational class. Every transaction must satisfy a conservation constraint (outputs cannot exceed inputs), and the total system value is bounded. These two constraints — conservation and boundedness — create a computational model that sits in a specific and previously uncharacterized place in the landscape of formal automata.

Three contributions were outlined in a two-page proposal:

1. **BRA as a computational class**: Define the automata, prove finiteness of value-only BRA, prove infiniteness of identity-tracking BRA, establish Petri net correspondence.
2. **Collapse functor**: Construct a categorical functor mapping Bitcoin's UTXO model to Ethereum's account model. Characterize what information is lost.
3. **Conservation as structural invariant**: Show that total value is preserved across the functor.

Lean 4 was chosen as the verification tool. The author — a systems science PhD student, not a proof engineer — had never written a line of Lean. The methodology was what Jacopo Tagliabue would independently coin "vibe proving": the human steers, the LLM writes Lean, the compiler checks. Three roles, three kinds of authority.

A literature search revealed prior art: Nester (2020) on symmetric monoidal categories as resource theories, Lambert (2021) on topos-theoretic consensus, Swan (2024) on categorical blockchain semantics. The gap: no one had defined the computational class from conservation constraints. No one had proved the separation results. No one had built the comparison functor.

---

## 3. Day 1: Bitcoin-BRA Takes Shape

*February 16, 2026*

The first Lean session began with a single file: `BRA/Basic.lean`. Getting it to compile required fixing nine separate issues — bad imports, missing instances, scoping problems, notation resolution failures. Session 1 ended at 601 jobs, 0 errors, 0 warnings, 0 `sorry`s. One file.

Then the finiteness proofs. The key theorem: for bound *C*, the number of BRA states is finite, with cardinality at most *(C+1)^C*. The proof strategy: inject states into histograms (functions from values to bounded counts), then use `Fintype.ofInjective`. Three problems solved in sequence — `Value C` is `Fintype`, the state size is bounded, the state space is finite.

By the end of Session 2, all Tier 1 problems were complete. The `sorry` count dropped from 7 to 1 (only a transition function construction remained). The proofs accumulated:

- `conservation_commutes`: multiset induction on the UTXO set
- `collapse_not_injective`: concrete witness with two UTXO sets that collapse to the same balance
- `collapse_surjective`: induction on `Finsupp` using `Finsupp.induction`
- `itstate_infinite`: injection from naturals via fresh identity creation
- `conservation_functor`: the original natural-number form was mathematically wrong (truncated subtraction); the additive form fixed it

Session 3 cleared the last `sorry`. The Petri net correspondence was proved — the weighted place invariant `w(p) = p+1` bridges BRA states to bounded Petri net markings. Every claim in the codebase was machine-checked.

**Zero `sorry`s. 893 jobs. 0 errors.**

Session 4 produced the paper draft: 7,950 words, 11 sections, 62 theorem references verified against Lean source. Session 5 converted it to LaTeX for CPP 2027. Session 6 applied ten editorial revisions. All on the same day.

The verification loop that made this possible:

- **Human**: editorial judgment, interpretation choices, recognizing when output was type-correct but conceptually wrong
- **LLM**: Lean syntax fluency, Mathlib API navigation, tactic proof generation
- **Compiler**: final authority — zero `sorry`s means every claim is machine-checked

The hard problems were never proof search. No proof required more than a few tactic steps. They were *representational*: should we use `Multiset` or `Finset`? Should `Value` be a `Subtype` or `Fin`? Should `collapse` use `foldl` or `Multiset.sum ∘ Multiset.map`? These decisions propagate through the entire codebase. They require understanding the mathematics, not Lean expertise.

---

## 4. Day 2 Morning: Publication

*February 17, 2026 — AM*

The LaTeX paper was built, the editorial revisions applied, the GitHub repository published. Final statistics:

- 882 lines of Lean 4 across 7 files
- 74 declarations
- Zero `sorry`s
- 14 references
- Target: CPP 2027

The paper's title: "What Bitcoin Can and Cannot Compute: Verified Separation Results for Conservation-Constrained Automata."

Between Session 5 and Session 6, something else happened. Shingai discovered Jacopo Tagliabue's blog posts coining the term "vibe proving" — independently naming exactly the methodology being used. The same workflow. The same trust distribution. An outreach email was drafted. The methodology had a name and a community.

---

## 5. Day 2 Afternoon: The Pivot

*February 17, 2026 — PM*

With the BRA paper published, the question shifted. The Bitcoin formalization was complete. But the methodology — LLM-assisted formal verification guided by domain expertise — had just been demonstrated to work. Could it extend to the author's actual research domain?

The domain: systems ontology. Specifically, three independently developed frameworks for defining what a "system" is:

- **Klir (1969/2001)**: A system is a set of things and a relation. `S = (T, R)`.
- **Bunge (1979)**: A system is a composition, environment, and structure. `⟨C, E, S⟩`. Adds environment to Klir.
- **Mobus (2022)**: A system is an eight-component tuple. `⟨C, N, E, G, B, T, H, Δt⟩`. Adds typed flows, boundary, milieu, transforms, history, and time scale to Klir.

Neither Bunge nor Mobus references the other. They developed independently, 43 years apart, from the shared Klir root. One philosophical, one engineering.

The author's position to connect them was biographical, not mathematical. His advisor, Cliff Joslyn, was Klir's PhD student. He had built a software tool (BERT) implementing Mobus's framework. And now he had a proof assistant.

The systems-ontology project was initialized.

---

## 6. The Discovery

*February 17, 2026 — evening, into February 18*

Phase 1 formalized Bunge's *Treatise on Basic Philosophy* Vol. 4, Chapter 1: 864 lines, 7 core modules, 74 declarations. The type-checker forced decisions on every ambiguity in Bunge's prose — and there were many.

The most immediate finding: Bunge's Definition 1.6 describes the subsystem relation as "reflexive, asymmetric, and transitive." A relation cannot be both reflexive and asymmetric. Reflexivity gives *a ≤ a*; asymmetry says *a ≤ b* and *b ≤ a* implies *a ≠ b*. Applied to *a = a*: contradiction. He means *antisymmetric* — a partial order. In print for 47 years. The proof assistant caught it immediately.

Phase 2 formalized Mobus's eight-tuple: 886 lines, 6 modules. The bridge theorem (`toBunge`) showed that every Mobus system projects to a valid Bunge CES triple, with six formally characterized categories of information lost in the projection.

Then Phase 3: Klir's common root. 146 lines. One module. And the central discovery.

The commuting triangle: both paths from Mobus's 8-tuple back to Klir's `(T, R)` produce *definitionally identical* results. Not isomorphic. Not equivalent up to some transformation. Identical. The proof is the Lean keyword `rfl` — reflexivity — meaning the compiler checked that the two expressions evaluate to the same term without any computation.

The `rfl` proofs trace to both authors inheriting `T = Set α` and `R = Set (α × α)` from Klir without changing the mathematical type. They elaborated independently for 43 years, adding wildly different structure, but never modified the foundation. The compatibility was not claimed by any of the three authors. It was *discovered* through formalization.

And then the intellectual genealogy suddenly had mathematical content. Klir defined `S = (T, R)`. Klir taught Joslyn. Joslyn taught the author. Mobus cited Klir. Bunge cited Klir. The author — sitting at the intersection of all three traditions — proved they form a commuting triangle. The proof assistant made visible the mathematical structure of an intellectual lineage.

---

## 7. Categorification

*February 18, 2026*

The categorification was expected to take weeks. The roadmap outlined three phases with careful CatLab.jl prototyping before Lean formalization. Phase 1 completed in hours.

**Subsystem orderings as categories.** Three natural ways to order systems — by family (tracking individual relations), by refinement (requiring coarsenings), and flat (using the union) — each define a thin category. The forgetful functors between them are faithful but not full: explicit counterexamples on `Fin 2` prove each step is strict. This is Finding 8 from the StructureFamily exploration, now elevated from a set-theoretic observation to a categorical theorem.

**Bridge factorization.** The Mobus-to-Bunge bridge factors through the structure family: `toBunge = toRichBunge ⋙ flatten`. A theorem about the relationship between frameworks that neither author stated.

**The collapse functor.** Back in bitcoin-bra, the plain `collapse` function was upgraded to a proper Mathlib functor `collapseFunctor : BtcState ⥤ EthState`. Essentially surjective (`EssSurj`). Not faithful — the first genuinely new result requiring categories. Two distinct UTXO operations (consuming and reproducing different UTXOs) are distinguishable in Bitcoin-land but invisible at the balance level. The functor maps both to the unique identity morphism in the thin Ethereum category. `¬Faithful` is not statable without `Category` instances.

**Conservation commutes at the functor-object level.** `totalValue ∘ collapse = totalValue`.

Then Phase 3 pushed into exploratory territory:

**Polynomial functors** mapped 5–6 of Mobus's 8 tuple components to Spivak's framework. The boundary-interface-flow triangle maps cleanly. Time scale and milieu have no counterpart — they are engineering concepts that no purely algebraic framework captures.

**Operad algebras** corrected Bunge. His §1.6 states: "the set of all systems has no algebraic structure — not even the rather modest one of a semigroup." He's right about semigroups — not every pair of systems can compose. But the partiality of composition *is* the structure, not the absence of it. Two systems compose when their boundaries match: a producer's output leg glues to a consumer's input leg along a shared species. The patterns of which systems can compose with which — the "shapes" of legal compositions — form an operad. Systems are an operad algebra: they carry structure richer than a semigroup, precisely because composition is typed by boundary compatibility rather than universally defined. Verified computationally with AlgebraicPetri.jl: sequential composition, parallel composition, and associativity all confirmed. This is a genuine correction to a foundational text — Bunge diagnosed the right intuition (systems don't compose freely) but drew the wrong conclusion (therefore no algebraic structure exists).

**Petri net correspondence** showed BRA transactions translate directly to bounded Petri nets with a weighted place invariant. Open Petri net composition provides the compositional structure the Lean formalization doesn't yet have.

The combined statistics at this point:

| | Systems Ontology | Bitcoin-BRA | Total |
|---|---|---|---|
| Lines | ~2,930 | ~1,080 | ~4,010 |
| Modules/Files | 20 | 11 | 31 |
| `sorry`s | 0 | 0 | 0 |

---

## 8. The Realization

Then Shingai stepped back.

> *"I'm reeling. I'm not a mathematician."*

He took a walk. Didn't touch files. Came back calmer, with perspective.

The "not a mathematician" thread runs through the entire 48 hours. It appears in the first conversation ("this is an exercise in seeing how far an LLM can take this") and in the last ("I'm reeling"). The tension is productive. It's precisely because the author is not a proof engineer that the methodology matters. Domain expertise — knowing *what questions to ask* — is the irreplaceable ingredient. A mathematician might have formalized any one of these frameworks. It took a systems scientist to ask whether they commute.

Each step was driven by a question:

- *"Is this paper's math real?"* — No, but the observations underneath are.
- *"What would rigorous math look like?"* — BRA framework.
- *"Can a proof assistant verify this?"* — Yes, 882 lines, zero `sorry`s.
- *"Can this methodology extend to my actual research?"* — Yes, 2,930 more lines.
- *"How do these frameworks relate?"* — Commuting triangle, Klir as common ancestor.
- *"What does the structure really look like categorically?"* — Functors, not-faithful collapse, operadic composition.
- *"What does this mean for the field?"* — The algebraic backbone for integration that everyone thought didn't exist.

The proof assistant didn't answer these questions. Shingai asked them. The proof assistant verified the answers.

48 hours is not the point. The point is the methodology: curiosity → critique → construction → discovery → integration. The 48 hours demonstrate that the bottleneck in formal verification of domain knowledge is not proof engineering. It is knowing what to prove.

---

## Origins

Everything traces back further than February 16. In the summer of 2025, Shingai wrote a paper applying Klir's framework to Bitcoin and Ethereum empirically — the TBS Presentation notebook, now in `refs/TBS_Presentation.ipynb`. His advisor Cliff Joslyn reviewed it and left approximately 30 red-text comments on the PDF (`refs/Thornton_IS_Summer_2025.pdf`). Comment A1 asked, in essence: *"S is a set of sets of tuples, right?"*

That question — an advisor's marginal annotation on a student's summer paper — is the true origin of the entire project. Thirteen of Joslyn's thirty comments map directly to formalized code. The compiler retroactively answered most of them.

The intellectual lineage:

```
Klir (1969) ─── S = (T, R) ─── the seed
   │
   ├── Bunge (1979) ── cites Klir → adds Environment
   │
   ├── Mobus (2022) ── cites Klir → adds flows, boundary, milieu
   │
   └── Joslyn (PhD student of Klir)
            │
            └── Shingai (student of Joslyn)
                    │
                    ├── Built BERT on Mobus
                    ├── Formalized Bunge
                    └── Proved the commuting triangle
```

The commuting triangle is the formal structure of an intellectual tradition made visible by a proof assistant.

---

## Source Files

- [bitcoin-bra](../bitcoin-bra/) — BRA formalization (~1,080 lines, 11 files, targeting CPP 2027)
- [systems-ontology](../) — Systems ontology formalization (~2,930 lines, 20 modules)
- [categorification-roadmap.md](../categorification-roadmap.md) — Phase tracking across both projects
- [categorification-story.html](categorification-story.html) — Technical companion: the categorical results in detail
- [phase1-retrospective.md](phase1-retrospective.md) — Where Lean forced choices on Bunge's text
- [phase3-exploration-log.md](phase3-exploration-log.md) — Polynomial functors, operads, and the AlgebraicJulia bridge
- [bitcoin-bra/notes/session_log.md](../bitcoin-bra/notes/session_log.md) — 7 sessions of technical proof details

---

*Built with Lean 4, Mathlib, and a proof assistant that doesn't care about your reputation — only your types.*
