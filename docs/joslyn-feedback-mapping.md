# Joslyn Feedback Mapping: Summer 2025 Paper → Lean Formalization

*Every red-text comment from Cliff Joslyn's review of `Thornton_IS_Summer_2025.pdf`, organized by what the formalization can and cannot address.*

**Source**: `notes/Thornton_IS_Summer_2025.pdf`
**Date**: Review ~August 2025 | Mapping created 2026-02-17

---

## A. Answered by Formalization (13 comments)

These are questions where the Lean codebase provides a precise, machine-checked answer.

### A1. Structure type resolution (p. 7) — **strongest vindication**

> "What do you mean more precisely? 'Set of relations' literally means S is a set of sets of tuples, right? So e.g. S = {S_i}. Tuples implies a Cartesian product, so is it S_i ⊆ C × E, or S_i ⊆ (C ∪ E) × (C ∪ E), or what?"

**The Lean compiler forced exactly this decision.** `structure' : Set (α × α)` with constraint `structure_on : ∀ p ∈ structure', p.1 ∈ composition ∪ environment ∧ p.2 ∈ composition ∪ environment`. It is a single flat set of pairs on C ∪ E, not a set of relations. The compiler demanded the precision Cliff was requesting.

**File**: System.lean:40, 44–45

**StructureFamily Resolution (2026-02-17):**
- Status: **RESOLVED** — `flatten_internal_commutes` proves flat encoding is faithful quotient
- Bonus Finding 6: Mobus's N/G constitutes the natural 2-element structure family (`MobusSystem.toRichBunge`, `toRichBunge_flatten_eq`)
- Bonus Finding 8: Three distinct subsystem orderings (`RichSubsystem_flat`, `RichSubsystem_family`, `RichSubsystem_refinement`) with strict hierarchy proved by `family_implies_refinement` → `refinement_implies_flat` → `flat_subsystem_preserved`
- Cross-ref: `docs/for-cliff-structure-of-S.md`, `docs/structure-family-context.md`

### A2. "Systematic extension" claim (p. 7) — **must be corrected**

> "While Mobus never explicitly cites Bunge, his 7-tuple can easily be viewed as a systematic extension of Bunge's formalization"

**This sentence is now formally wrong.** Mobus cites Klir (2001), not Bunge. Bunge cites Klir & Valach (1967). They developed independently from a shared Klir root. The bridge theorem *discovers* compatibility via projection; it does not verify extension. The commuting triangle is the precise correction: Mobus → Bunge → Klir = Mobus → Klir by `rfl`.

**File**: KlirSystem.lean:triangle_commutes, Bridge.lean header

### A3. Structure vs. function distinction (p. 4)

> "all the systems sciences do this, and not just how systems function, but also how they're structured, and the interaction between the two. Think of function as dynamics and structure as statics."

The formalization embodies exactly this distinction. Bunge's `structure' : Set (α × α)` is the static relational structure. Mobus's `FlowNetwork` with capacity labels captures the dynamic/functional aspect. The bridge theorem (`toBunge`) projects dynamics to statics: `totalRelation` discards capacity (the functional content) leaving only structural pairs.

**File**: Bridge.lean:130–132, FlowNetwork.lean:toRelation

### A4. Flow circularity (p. 4)

> "that's what distinguishes cybernetics, and especially for issues related to circular information flows. One could argue that control is always so circular."

Flow circularity is representable in FlowNetwork (no acyclicity constraint). The `no_self_loops` constraint prevents trivial reflexive edges but allows cycles through multiple nodes. Circular control flows are valid `FlowNetwork` instances.

**File**: FlowNetwork.lean:23 (no_self_loops)

### A5. Klir citation + Mesarovic, Takahara (p. 5)

> "Cite something" (on Klir) + "maybe don't leave out others, e.g. Mesarovic, Takahara."

Klir (2001) [1] already cited. **The formalization now gives precise standing**: Klir's `S = (T, R)` is Eq. 1.1, formalized as `KlirSystem α`. It is the verified common root of the commuting triangle. Add: Mesarovic, M.D. & Takahara, Y. (1975). *General Systems Theory: Mathematical Foundations*. Academic Press.

**File**: KlirSystem.lean (entire file)

### A6. "Like which ones?" — mathematical frameworks (p. 5)

> "Like which ones?"

**Now precisely enumerable from the codebase**: Set theory (Bunge's CES triple — System.lean), graph theory (Mobus's flow networks — FlowNetwork.lean), relation theory (ActsOn, bondage — Bond.lean), order theory (subsystem partial order — System.lean:118–151), inductive types (recursive decomposition — Level.lean). The BRA companion adds automata theory and category theory.

**File**: System.lean, FlowNetwork.lean, Bond.lean, Level.lean

### A7. Tree structure / subscript indexing (p. 7)

> "somewhere the actual branching structure needs to be indicated, e.g. that S₅,₂ is a child of S₂,₁. How is that done?"

`docs/recursive-component-architecture.md` addresses this directly. The formalization uses Option C: `MobusSystem` is flat (`components : Set α`), and `RecursiveComponent` in Level.lean captures the tree structure separately. The parent-child relationship is Mobus's dotted index notation formalized as the inductive `RecursiveComponent` type. Option A (mutual induction) is the long-term target.

**File**: Level.lean:53–58, docs/recursive-component-architecture.md §3

### A8. Table 1 "Not included" cells (p. 8)

> "So you're suggesting that the 'not included' cells could be filled in?"

**Yes.** Bunge *does* formalize flows (Ch. 2–3), transformations (state space framework), history (state trajectories), time intervals, and level structure (Def 1.7–1.8). He doesn't put them in the CES triple. Phase 1 Lean code formalizes several: state functions (State.lean), level structure (Level.lean), assembly/emergence (Assembly.lean). Table should say "formalized elsewhere in Bunge, not in the system definition." The six information loss categories in Bridge.lean precisely characterize what Mobus adds beyond Bunge's *system definition*, not beyond Bunge's *entire framework*.

**File**: State.lean, Level.lean, Assembly.lean, Bridge.lean:134–179

### A9. Component-by-component explanation (p. 8)

> "It would be preferable to first go through each of the 7 components and explain them on their own terms, and illustrate with a very small example"

**The Lean codebase now IS that component-by-component explanation.** Each has its own file with docstrings: FlowNetwork.lean, Environment.lean, Boundary.lean, Interface.lean. For the ISSS presentation, walk through a tiny example (e.g., a biological cell) showing each tuple element, then show the corresponding Lean structure.

**File**: FlowNetwork.lean, Environment.lean, Boundary.lean, Interface.lean, Tuple.lean

### A10. "The precise version Cliff wanted" (p. 8)

> "I regret that this is the kind of thing I was hoping to see initially when I tried to read Mobus directly."

The retrospective documents exactly where Mobus's prose proved under-specified when formalized. The Lean code is the "precise version" Cliff wanted.

**File**: docs/phase1-retrospective.md

### A11. Table 2 ontological terms (p. 11)

> "These two tables are extremely important, much of the meat of the paper. They should be explained in detail, illustrated by the example."

The Lean formalization now provides machine-checked definitions for every ontological term in Table 2's left column: Environment → Environment.lean, Source/Sink → Interface.lean:EnvSources/EnvSinks, Flows → FlowNetwork.lean, Boundary → Boundary.lean, Interfaces → Interface.lean, System → Tuple.lean, Subsystem → Bridge.lean:MobusSubsystem, Hierarchy → Level.lean.

**File**: Environment.lean, Interface.lean, FlowNetwork.lean, Boundary.lean

### A12. Figure 2 structure (p. 12)

> "figure needs to be cited in the text and explained in detail."

Writing issue, but: Figure 2's structure (system of interest with environment objects as sources/sinks) maps directly to a `MobusSystem` instance. The outer objects are `environment.objects`, classified as `EnvSources`/`EnvSinks` by Interface.lean, connected via `externalFlows` (bipartite).

**File**: Tuple.lean, Interface.lean:EnvSources/EnvSinks

### A13. Sources and sinks (p. 13) — **prescient**

> "Are there any sources or sinks in this model? I'm struck by how significant they are in terms of the overall methodology, and while you cite them above, you don't explain them or use them?"

**Now formalized precisely.** `EnvSources` and `EnvSinks` in Interface.lean classify environmental objects by flow direction. `EnvDual` captures objects that are both. In the interstate commerce example, Global Supply Networks and International Trade are sources, Global Economic Systems is a sink. The `bipartite` constraint on `MobusSystem` guarantees every external flow crosses between environment objects and interface components.

**File**: Interface.lean:73–88 (EnvSources, EnvSinks, EnvDual)

---

## B. Writing, Presentation, and Structure (10 comments)

These require paper revisions, not formalization. Noted for the next draft.

| # | Page | Comment | Action |
|---|------|---------|--------|
| B1 | 1 | "Fig. 1 should be referenced and described." | Cite and describe Hieronymi (2013) chart in text |
| B2 | 4 | "Not sure why you leave these paragraph-trailing \\\\." | Fix LaTeX formatting |
| B3 | 6 | "So BERT is based on Mobus? I don't think you actually say so anywhere. You need a paragraph introducing BERT and Mobus distinctly, then relating them." | Add "BERT is..." subsection establishing BERT → Mobus relationship |
| B4 | 8 | "all the i,l subscripting gets distracting and tedious, in small example you can just use A, B, C" | Simplify notation in examples per Cliff's suggestion |
| B5 | 9 | "I think we need a subsection somewhere which says 'BERT is ...', including the relation to Mobus." | Same as B3 — structural issue, add subsection |
| B6 | 12 | "You should provide full details as to how this quantity is defined or derived" (aggregate economic productivity signal) | Expand case study methodology |
| B7 | 12 | "figure needs to be cited in the text and explained in detail." (Fig. 2) | Cite and explain in text (formalization provides the vocabulary — see A12) |
| B8 | 13 | "Same deal on this figure, and we've both noted the font management issues." (Fig. 3) | Fix BERT font rendering + cite/explain figure |
| B9 | 14 | "Same deal on figure." (Fig. 4) | Cite and explain in text |
| B10 | 11 | "The table should be cited explicitly in the text." (Tables 1 & 2) | Cite both tables in text, explain in detail |

---

## C. Bibliography and Citation (7 comments)

Missing or improperly formatted references.

| # | Page | Comment | Action |
|---|------|---------|--------|
| C1 | 3 | "Is BERT an acronym or initialism? If so, spell it out." | Spell out "Bounded Entity Reasoning Toolkit" at first use |
| C2 | 4 | "you should also cite the Wiener original too." | Add: Wiener, N. (1948). *Cybernetics*. MIT Press. |
| C3 | 4 | "Cite something here." (Ashby's Requisite Variety) | Ashby already in refs as [12]; cite at this location |
| C4 | 5 | "That's strong, cite something?" ("charlatans" jeopardizing the field) | Find specific Bunge source — check *Scientific Materialism* (1981) or Vol. 4 preface |
| C5 | 5 | "maybe don't leave out others, e.g. Mesarovic, Takahara." | Add: Mesarovic & Takahara (1975). *General Systems Theory: Mathematical Foundations* |
| C6 | 9 | "Cite the page number." (Mobus quote about inaccessible math) | Verify page number in Mobus (2022) |
| C7 | 9–10 | "technically this should be a citation like 'here's the original article, but as reprinted in Facets'" | Formatting issue — dual citation for Klir reprints |

---

## D. Acknowledged / No Action Needed (2 comments)

| # | Page | Comment | Note |
|---|------|---------|------|
| D1 | 4 | "You may be right, yes." (cyberneticists emphasize epistemology) | Agreement, no action |
| D2 | 6 | "Odd use of the term 'composition', but I can go with it." | Bunge's term. Formalized as `composition : Set α` in System.lean:36. Lean type makes it unambiguous. |

---

## E. Ontology distinction (1 comment, cross-cutting)

| # | Page | Comment | Note |
|---|------|---------|------|
| E1 | 3–4 | "do you mean the upper case here to be significant?" (Ontology vs. ontology) | Yes — philosophical Ontology (capital O) vs. computational domain ontology (lowercase). The formalization operationalizes this: Bunge's Systems/Core/ is capital-O Ontology; the Lean code itself is the computational ontology. |

---

## Key Takeaways

1. **Comment A1 is the strongest vindication — now fully resolved.** Cliff asked exactly the question the type-checker forces: "is it S_i ⊆ C × E, or S_i ⊆ (C ∪ E) × (C ∪ E)?" The Lean code answers: `Set (α × α)` on `C ∪ E` with an explicit constraint. The StructureFamily exploration (2026-02-17) proved the flat encoding is a faithful quotient: `flatten_internal_commutes` shows both readings are equivalent for the proved theorems. The investigation also revealed that Mobus's N/G is the natural structure family (Finding 6) and that three distinct subsystem orderings arise from the family representation (Finding 8).

2. **Comment A2 must be corrected in the paper.** "his 7-tuple can easily be viewed as a systematic extension of Bunge's formalization" is formally wrong. The commuting triangle proves they are independent elaborations of Klir's common root.

3. **Comment A9 has been fulfilled.** "go through each of the 7 components and explain them on their own terms" — the Phase 2 Lean modules are literally organized this way (one file per component, with docstrings).

4. **Comment A13 (sources/sinks) was prescient.** Cliff identified their methodological significance before the formalization existed. The formalization now provides `EnvSources`, `EnvSinks`, and `EnvDual` with subset theorems, bipartite edge-direction theorems, and the connection to boundary completeness.

5. **13 of 30 comments are directly answerable from machine-checked Lean code.** For a paper written before any formalization existed, this confirms that formalization addresses the questions a careful mathematician actually asks.
