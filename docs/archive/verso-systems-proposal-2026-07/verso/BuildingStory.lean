import VersoManual

open Verso.Genre Manual

#doc (Manual) "Building Story" =>

%%%
authors := ["Shingai Thornton"]
%%%

*From a flawed paper to ~4,700 lines of certified mathematics — a 48-hour arc of curiosity, critique, construction, discovery, and integration.*

# The Spark

It began with a 222-page paper claiming that Bitcoin reveals fundamental physics. The mathematical observations underneath were real — Bitcoin's UTXO set genuinely has interesting computational structure — but the physics framing was wrong. The pivotal moment came from a single question: not "how do I critique this paper?" but *"what's the REAL mathematics here?"*

That question changed everything. Instead of a critique, it became a construction.

# Day 1: Bitcoin-BRA Takes Shape

The answer was a framework called *Bounded-Resource Automata* (BRA). The core insight: Bitcoin's UTXO model defines a novel computational class. Every transaction must satisfy a conservation constraint (outputs cannot exceed inputs), and the total system value is bounded.

Lean 4 was chosen as the verification tool. The author — a systems science PhD student, not a proof engineer — had never written a line of Lean. The methodology was what Jacopo Tagliabue would independently coin "vibe proving": the human steers, the LLM writes Lean, the compiler checks. Three roles, three kinds of authority.

By the end of Day 1: 893 build jobs, 0 errors, 0 `sorry`s. Paper draft written. LaTeX converted. All in one day.

# Day 2: The Pivot

With the BRA paper published, the question shifted. Could the methodology extend to the author's actual research domain?

The domain: systems ontology. Three independently developed frameworks for defining what a "system" is — Klir (1969), Bunge (1979), Mobus (2022). Neither Bunge nor Mobus references the other. They developed independently, 43 years apart, from the shared Klir root.

The author's position to connect them was biographical, not mathematical. His advisor, Cliff Joslyn, was Klir's PhD student. He had built a software tool (BERT) implementing Mobus's framework. And now he had a proof assistant.

# The Discovery

Phase 1 formalized Bunge: 864 lines, 7 modules. The type-checker forced decisions on every ambiguity in the prose — and caught a 47-year-old error (Bunge's "asymmetric" should be "antisymmetric"). Phase 2 formalized Mobus's 8-tuple: 886 lines, 6 modules. The bridge theorem showed every Mobus system projects to a valid Bunge CES triple.

Then Phase 3: Klir's common root. 146 lines. One module. And the central discovery: both paths from Mobus's 8-tuple back to Klir's (T, R) produce *definitionally identical* results. The proof is `rfl`. This was not claimed by any of the three authors. It was discovered through formalization.

# Categorification

The categorification was expected to take weeks. Phase 1 completed in hours.

The ordering triangle: three natural ways to order systems, each defining a thin category. Forgetful functors between them are faithful but not full — explicit counterexamples prove each step is strict.

The bridge factorization: `toBunge = toRichBunge ⋙ flatten`. A theorem about the relationship between frameworks that neither author stated.

Shape categories: each tradition's definition encoded as a free category on its dependency quiver. Seven traditions, seven shapes, one common core — Klir's walking arrow **2** embeds into all of them.

# The Realization

Then the author stepped back. "I'm reeling. I'm not a mathematician."

The tension is productive. It's precisely because the author is not a proof engineer that the methodology matters. Domain expertise — knowing *what questions to ask* — is the irreplaceable ingredient. A mathematician might have formalized any one of these frameworks. It took a systems scientist to ask whether they commute.

Each step was driven by a question:

- "Is this paper's math real?" — No, but the observations underneath are.
- "What would rigorous math look like?" — BRA framework.
- "Can a proof assistant verify this?" — Yes, 882 lines, zero `sorry`s.
- "Can this extend to my actual research?" — Yes, ~3,000 more lines.
- "How do these frameworks relate?" — Commuting triangle.
- "What does the structure look like categorically?" — Functors, operads, shape categories.

# Origins

Everything traces back further than February 16, 2026. In summer 2025, the author wrote a paper applying Klir's framework to Bitcoin and Ethereum empirically. His advisor Cliff Joslyn reviewed it and left approximately 30 red-text comments. Comment A1 asked: *"S is a set of sets of tuples, right?"*

That question — an advisor's marginal annotation on a student's summer paper — is the true origin of the entire project. Thirteen of Joslyn's thirty comments map directly to formalized code. The compiler retroactively answered most of them.

The proof assistant didn't answer these questions. The author asked them. The proof assistant verified the answers.

48 hours is not the point. The point is the methodology: curiosity → critique → construction → discovery → integration. The bottleneck in formal verification of domain knowledge is not proof engineering. It is knowing what to prove.
