# What Happens When You Type-Check Bunge: Formal Verification of Systems Ontology Using AI-Assisted Theorem Proving

**Venue**: ISSS 2026 — 70th Annual Meeting of the International Society for the Systems Sciences
**Format**: Presentation abstract
**Status**: Draft

---

We formalized the core of Bunge's systems ontology (*Treatise on Basic Philosophy* Vol. 4, Ch. 1) in the Lean 4 proof assistant, producing 864 lines of machine-verified mathematics: the CES (Composition–Environment–Structure) triple, subsystem partial order, assembly and emergence, selective action, level structure, and state functions — 19 definitions, 8 postulates, and 3 theorems checked against formal logic. We then independently formalized Mobus's 8-tuple system definition (*Understanding Systems* Ch. 4, plus 2024 book-revisions) in 882 lines: components, flow networks, environment with parametric milieu, boundary with interfaces, bipartite external flows, transforms, history, and time scale. The entire codebase compiles with zero unproved assertions (`sorry`s).

**Main result.** Bunge (1979) and Mobus (2022) developed their frameworks independently — neither author references the other, and 43 years separate their publications. Our bridge theorem proves that every well-formed Mobus 8-tuple projects to a valid Bunge CES triple: components map to composition (exactly), environment objects map to environment (milieu discarded), and the union of internal and external flow relations maps to structure (capacity labels discarded). This is not verification of a claimed relationship. It is *discovery*, through formalization, of a structural compatibility between two traditions that arrived at the concept of "system" from different starting points — philosophical ontology and engineering systems science — and converged on the same decomposition.

The divergence is equally informative. Six categories of information present in Mobus's 8-tuple have no Bunge counterpart and are projected away: milieu (ambient environmental variables), capacity (quantitative flow labels), boundary properties, transforms, history, and time scale. These loss categories mark the precise points where Mobus's engineering orientation led to distinctions that Bunge's philosophical orientation did not require. The formalization makes this divergence machine-checkable rather than interpretive.

**What the compiler revealed.** Typing Bunge's definitions into a proof assistant told us things about the ontology that 47 years of reading had not:

- *A logical error*: Bunge describes the subsystem relation (Def 1.6) as "reflexive, asymmetric, and transitive." A relation cannot be both reflexive and asymmetric. He means *antisymmetric* — a partial order. The proof assistant refuses to compile both properties simultaneously, catching an error in continuous print since 1979.

- *Cross-volume dependency architecture*: Corollary 1.1 ("the universe is the only closed system") is proved as a tautology — it is literally the definition of "closed." The substantive claim requires Postulate 5.10 from Vol. 3, a dependency invisible in the prose numbering but structurally undeniable in the type system.

- *Under-specification*: Bunge *defines* environment as derived from the bond relation, but the formalization must declare it as a free parameter — enforcing derivedness would require quantifying over all possible bonds. His `ActsOn` relation is defined via state-space trajectories, but the formalization reduces it to an opaque binary relation because the state-space semantics add no structural content at this level of abstraction. Each simplification is documented and justified, but each also marks a point where "precise-seeming" prose turns out to have degrees of freedom.

- *Clean compositions*: Selection composition (Bunge's Theorem 1.2) proves by definitional equality — the proof assistant needs no search because the definitions align perfectly. Emergence decomposes into set operations via a single `simp` tactic. These confirm Bunge's philosophical point (emergence is not mystical; it is set subtraction) through the compiler's own reasoning.

**Methodology.** The formalization was produced collaboratively with a large language model (Anthropic's Claude), aligning with this year's AI spotlight. The workflow: the human provides systems science domain expertise — what to formalize, which interpretation choices to make, when the AI is wrong — while the AI generates formal proofs in Lean 4 against the Mathlib mathematical library. The compiler verifies everything. This is a concrete demonstration of AI advancing systems science foundations: not by replacing human judgment, but by making the cost of formal verification low enough that a domain expert can produce machine-checked mathematics without years of proof assistant training.

**Operational grounding.** The formalized ontology is not purely theoretical. Mobus's framework is implemented in BERT (Bounded Entity Reasoning Toolkit, halcyonic.systems), a working systems analysis application. The Lean proofs provide machine-verified foundations for the same concepts the tool implements visually — formal ontology grounding operational software.

**Keywords**: systems ontology, formal verification, Bunge, Mobus, Lean 4, CES triple, independent convergence, AI-assisted theorem proving

---

### References

Bunge, M. (1979). *Treatise on Basic Philosophy*, Vol. 4: *A World of Systems*. Dordrecht: Reidel.

Mobus, G.E. (2022). *Understanding Systems: A Grand Challenge for 21st-Century Engineering*. Cham: Springer.

Mobus, G.E. (2024). Book revisions to the 8-tuple system definition. Personal communication.

de Moura, L. & Ullrich, S. (2021). The Lean 4 theorem prover and programming language. *CADE-28*.
