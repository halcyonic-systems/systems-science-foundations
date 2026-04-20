# What Happens When You Type-Check Bunge: Machine Verification Reveals a Commuting Triangle from Klir to Mobus

**Venue**: ISSS 2026 --- 70th Annual Meeting of the International Society for the Systems Sciences
**Format**: Presentation abstract
**Status**: Draft

---

We formalized the core of Bunge's systems ontology (*Treatise on Basic Philosophy* Vol. 4, Ch. 1) in the Lean 4 proof assistant: 858 lines of machine-verified mathematics covering the CES triple, subsystem partial order, assembly and emergence, selective action, level structure, and state functions. We independently formalized Mobus's 8-tuple system definition (*Systems Science: Theory, Analysis, Modeling, and Design* Ch. 4, plus 2024 book-revisions) in 886 lines: components, flow networks, environment with parametric milieu, boundary with interfaces, transforms, history, and time scale. We then formalized Klir's foundational `S = (T, R)` (*Facets of Systems Science*, 2001, Eq. 1.1) and proved the commuting triangle. A categorification layer (563 lines, 4 modules) then packages subsystem orderings, flattening, and the Mobus-Bunge bridge as Mathlib functors and categories. The entire codebase --- ~2,930 lines across 20 Lean modules --- compiles with zero unproved assertions.

**Main result: a commuting triangle rooted in Klir.** Klir's `S = (T, R)` --- a set of things and a relation on those things --- is the common ancestor. Bunge cites Klir and Valach (1967) and Klir and Rogers (1977); he added environment as a third first-class component, producing the CES triple `<C, E, S>`. Mobus cites Klir (2001) explicitly as inspiration (Ch. 4, p. 14: "The development of this approach was inspired originally by Klir (2001)"); he elaborated the relation into typed flow networks with capacity labels, added boundary, interfaces, transforms, history, and time scale, producing the 8-tuple. Neither Bunge nor Mobus references the other. They developed independently from the shared Klir root.

The formalization proves: every Mobus 8-tuple projects to a valid Bunge CES triple (components to composition, environment objects to environment, total relation to structure). Every Bunge triple projects to a valid Klir system (forgetting environment). And the diagram *commutes* --- going Mobus to Bunge to Klir gives the same result as going Mobus to Klir directly. Three core fields transfer by *definitional equality*: the type-checker confirms they are literally the same mathematical object, not merely equivalent. For composition and structure, this traces to both authors inheriting T as a set of things and R as a set of pairs from Klir without changing the mathematical type. For environment, it traces to Mobus's environment carrying an `objects` field typed identically to Bunge's environment set --- a convergence not from Klir (who has no environment) but from both authors independently choosing the same representation for discrete environmental entities.

The six information loss categories in the Mobus-to-Bunge projection --- milieu, capacity, boundary properties, transforms, history, time scale --- mark precisely where Mobus's engineering orientation elaborated concepts that Bunge's philosophical orientation did not require. These are not deficiencies in either framework; they are the formal content of where two intellectual traditions diverge.

**The structure family: Mobus's N/G as the natural source.** Mobus's two-network design --- internal flow network N and bipartite external flow graph G --- constitutes the natural structure family. The `totalRelation` in the bridge theorem is literally ⋃₀{N.toRelation, G.toRelation} (`MobusSystem.toRichBunge_flatten_eq`). This makes visible an implicit relationship: Mobus's N/G separation is the *source* of the structure family; Bunge's flat S is the *target*. The bridge theorem was already performing this flattening --- it just wasn't labeled as such.

**What the compiler revealed.** Typing Bunge's definitions into a proof assistant told us things about the ontology that decades of reading had not. The compiler caught a logical error in Def 1.6: Bunge writes "reflexive, asymmetric, and transitive," but a relation cannot be both reflexive and asymmetric --- he means *antisymmetric*, a partial order. In print since 1979, uncaught until the proof assistant refused to compile it. The type system also exposed cross-volume dependency architecture (Corollary 1.1 is a tautology without Vol. 3's Postulate 5.10), and revealed points where precise-seeming prose turns out under-specified when formalized.

A reviewer asked whether the structure S should be typed as a set of sets of tuples --- Bunge's literal definition. The proof assistant verified that flattening commutes with internal/external decomposition (`flatten_internal_commutes`, `flatten_external_commutes`), making both readings equivalent for the proved theorems.

**Categorification: findings as functors.** After establishing the commuting triangle, we upgraded the key findings to categorical language using Mathlib's `CategoryTheory` library. The Mobus-to-Bunge bridge now factors as a functor composition: `bridge_factors_functor` proves that `toBunge = toRichBunge ⋙ flatten`, where `toRichBunge` embeds Mobus into the rich (family) representation and `flatten` is a Mathlib functor. This is the categorical content of the N/G structure family discovery: the bridge theorem was always a flattening functor --- it just wasn't labeled as such. Three subsystem orderings --- pointwise, refinement, and family --- are connected by faithful-but-not-full forgetful functors (`forgetFamily`, `forgetRefinement`), with explicit non-fullness witnesses on `Fin 2` (`not_full_forgetFamily`, `not_full_forgetRefinement`). "The choice of structure representation determines which subsystem category you inhabit" is now a compiler-certified theorem, not an informal observation. A companion BRA formalization (~1,080 lines) uses the same thin-category pattern to define a collapse functor from Bitcoin's UTXO model to Ethereum's account model (`collapseFunctor : BtcState ⥤ EthState`), proving essential surjectivity and non-faithfulness categorically.

**Methodology.** The formalization was produced collaboratively with a large language model (Anthropic's Claude), aligning with this year's AI spotlight. The human provides systems science domain expertise --- what to formalize, which interpretation choices to make, when the AI is wrong. The AI generates formal proofs; the compiler verifies everything. This demonstrates a concrete application of AI to advancing systems science foundations: making the cost of formal verification low enough that a domain expert can produce machine-checked mathematics without years of proof assistant training.

**Positioning.** To our knowledge, this is the first proof-assistant formalization of systems science foundations. Adjacent efforts --- Spivak and Fong's applied category theory for system composition, Guizzardi's Unified Foundational Ontology (which cites Bunge extensively but uses description logics, not proof assistants), INCOSE ontology stacks for digital engineering --- address related structures without machine verification. The intersection of systems science, proof assistants, and cross-framework comparison appears unoccupied.

**Operational grounding.** The formalized ontology is not purely theoretical. Mobus's framework is implemented in BERT (Bounded Entity Reasoning Toolkit, halcyonic.systems), a working systems analysis tool. The Lean proofs provide machine-verified foundations for the same concepts the tool implements visually. The methodological seed was a Python notebook applying Klir's `S = (T, R)` to Bitcoin and Ethereum network data under Joslyn's supervision --- the same framework now proved as the common root of the commuting triangle. The author's intellectual lineage --- Klir to Joslyn to the author, who built BERT on Mobus and formalized Bunge --- positions this work within the tradition it formalizes. The commuting triangle is not an accident; it is the formal structure of an intellectual tradition made visible by a proof assistant.

**Keywords**: systems ontology, formal verification, Klir, Bunge, Mobus, Lean 4, commuting triangle, CES triple, AI-assisted theorem proving, BERT

---

### References

Bunge, M. (1979). *Treatise on Basic Philosophy*, Vol. 4: *A World of Systems*. Dordrecht: Reidel.

Klir, G.J. (2001). *Facets of Systems Science*. 2nd ed. New York: Springer.

Mobus, G.E. (2022). *Systems Science: Theory, Analysis, Modeling, and Design*. Cham: Springer.

Mobus, G.E. (2024). Book revisions to the 8-tuple system definition. Personal communication.

de Moura, L. & Ullrich, S. (2021). The Lean 4 theorem prover and programming language. *CADE-28*.
