import VersoManual
import Systems.Category.CommonCore
import Systems.Category.SharedPrimitive
import Systems.Category.OrderingTriangle
import Systems.Category.BridgeFunctor
import Systems.Category.ShapeComparison
import Systems.Category.ShapeComparison_Myers
import Systems.Category.ShapeComparison_Wymore

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Systems

set_option pp.rawOnError true

#doc (Manual) "Categorification: Making Relationships Visible" =>

The commuting triangle tells us three structural traditions agree when projected to their common root. But the formalization now covers seven traditions across three orientations (structural, operational, and cybernetic). What about the *structure of the relationships themselves*? Category theory gives us the vocabulary to ask: when we say "Mobus refines Bunge," what *kind* of refinement is it? What is preserved, and what is forgotten?

# The Ordering Triangle

There are three natural ways to order systems by their subsystem relationships, depending on how much structure you track. The *family ordering* (tracking individual relations like N and G separately), the *refinement ordering* (requiring only that each relation has a coarsening), and the *flat ordering* (using only the union of all relations). Each defines a thin category. The forgetful functors between them are *faithful* (they don't create spurious relationships) but *not full* (they lose distinctions).

```lean
#check @instFaithfulForgetFamily
#check @not_full_forgetFamily
```

The non-fullness results are constructive: explicit witnesses on `Fin 2` (systems with just two elements) show that a refinement-subsystem pair need not be a family-subsystem pair, and a flat-subsystem pair need not be a refinement-subsystem pair. The choice of structure representation *determines which subsystem ordering you get* — different readers of these frameworks are implicitly working in different categories. This is not an academic distinction: practitioners in different traditions are often unknowingly disagreeing about ordering, not about systems.

# Bridge Factorization

The Mobus-to-Bunge bridge factors through the structure family representation. Mobus's separation of internal network (N) and external flows (G) *is* the natural two-element structure family. The bridge was always performing a flattening. The categorical language makes this visible:

`toBunge = toRichBunge ⋙ flatten`

```lean
#check @bridge_factors_functor
```

This factorization is a theorem about the *relationship between frameworks* that neither Bunge nor Mobus stated. The extended diagram commutes: the factorization composes with the bridge to Klir, extending the original commuting triangle through the intermediate structure family. Mobus's apparent complexity (eight components where Bunge needs three) is not arbitrary elaboration but a structured intermediate: the information exists in Bunge's framework implicitly; Mobus makes it addressable.

# Shape Categories and the Common Core

Each tradition's definition of "system" can be encoded as a *shape category* — a free category on the dependency quiver of its components. The shape captures what a tradition considers structurally relevant: which components exist and which depend on which.

Seven traditions yield seven shapes:

- $`I_{Klir}` — 2 objects, 1 arrow: the walking arrow *T → R* (things determine relations), the base case the reader met first
- $`I_{Bunge}` — 3 objects, 3 arrows: the CES dependency quiver, with the environment distinction Klir lacks
- $`I_{Mobus}` — 8 objects, 5 arrows + 3 isolated: the full 8-tuple whose coherence constraints the compiler enforced
- $`I_{Myers}` — 3 objects, 2 arrows: the lens/deterministic system pattern whose composition theorem proved compositionality
- $`I_{Wymore}` — 4 objects, 3 arrows: the engineer's state machine with admissible input function space
- $`I_{Mesarovic}` — 2-3 objects: the input/output base, maximum generality at the cost of internal opacity
- $`I_{Joslyn}` — 3 objects, 3 arrows: the cyclic feedback loop, the only tradition that formally distinguishes rule from law

The common core theorem proves that Klir's walking arrow $`\mathbf{2}` embeds faithfully into all seven shapes:

```lean
#check @klirToBunge
```

The embedding table shows exactly how the walking arrow's two objects — *things* and *relation* — map into each tradition's vocabulary:

| Target | things ↦ | relation ↦ | arrow ↦ |
|--------|----------|------------|---------|
| $`I_{Bunge}` | composition | structure | `struct_on_comp` |
| $`I_{Mobus}` | components | internalNetwork | `network_on_components` |
| $`I_{Myers}` | output | state | `expose` |
| $`I_{Wymore}` | output | state | `readout` |
| $`I_{Mesarovic}` | output | globalState | `response_output` |
| $`I_{Joslyn}` | controlled | effector | `efferent` |

Read the table row by row. For Bunge, *things* are composition and *relation* is structure — the walking arrow captures Bunge's foundational claim that structure is defined *over* composition. For Mobus, *things* are components and *relation* is the internal network — the same dependency that his first coherence constraint enforces (network nodes must equal components).

Then something shifts. For Myers, *things* are *output* and *relation* is *state*. The arrow reverses direction from the reader's expectation: where structural traditions say "relations depend on things," operational traditions say "state determines what you can observe." Wymore and Mesarovic make the same move. For Joslyn, *things* are the controlled variables and *relation* is the effector — the embedding picks one arc of the feedback loop. The afferent return has no counterpart in the walking arrow.

A structural divide emerges. Bunge and Mobus are *inward* — their arrows converge toward components. Myers, Wymore, and Mesarovic are *outward* — their arrows radiate from state. Joslyn is the only *cyclic* tradition — feedback generates infinitely many morphisms in the free category. All other shapes are acyclic. Same arrow, three orientations. The divergence is the history of systems science.

Two shapes joined the landscape after this section was first written, and the argument below needs both. $`I_{Spivak}` — 4 objects, 5 arrows, the second cyclic shape, feedback through *value* rather than through observation. $`I_{Willems}` — 3 objects, 2 arrows, the behavioral triple, admitted as a stress test because it is the tradition most hostile to input/output orientation. Both carry the walking arrow. Eight shapes in total.

*Is it maximal?* The obvious argument runs: `KlirPosition` has two elements, so by pigeonhole nothing with three objects embeds into Klir, so nothing larger is shared. That argument is circular, because it treats Klir as one of the targets and thereby reduces a claim about eight traditions to a claim about $`\mathbf{2}` alone. It is also false. Faithfulness constrains hom-sets, not objects: the three-object chain is thin and connected and maps faithfully into $`\mathbf{2}` by collapsing two objects.

Strengthening to _faithful and injective on objects_ does not rescue it. Let $`V` be the fork — one source, two arrows, two distinct sinks. $`V` is connected, has three objects, and embeds into all eight shape categories that way.

The leak is the sentence above about Joslyn. Feedback generates infinitely many morphisms in the free category, and $`V` walks in through one of them: there is no _arrow_ controller $`\to` controlled, but there is a _path_, and in a free category every path is a morphism. $`V` enters through a dependency the tradition never asserts.

```lean
#check @SharedPrimitive.free_category_maximality_fails
```

*The claim holds one level down.* Compare the dependency quivers rather than the free categories over them, so that edges must map to edges and derived composites stop counting. Then two traditions force the result and the other six are not needed: no vertex of Joslyn's quiver has out-degree two, and Willems' quiver has no vertex of in-degree two and no composable pair of edges. Between them they exclude every two-edge connected configuration, so any two edges either coincide or share no vertex at all.

```lean
#check @SharedPrimitive.no_fork
#check @SharedPrimitive.no_cofork
#check @SharedPrimitive.no_two_chain
#check @SharedPrimitive.edges_coincide_or_disjoint
```

A connected quiver admitting such an embedding into every tradition therefore has exactly two vertices and one edge. Its free category is $`\mathbf{2}`.

So the honest statement is not that $`\mathbf{2}` is the largest category anything embeds into. It is that *the only dependency all eight traditions directly assert is one*. This is a claim about what the literature commits to, and it is accordingly relative to how each tradition is drawn here: adding a controller $`\to` controlled edge to Joslyn would readmit $`V`. Each edge is a documented primitive of its source text, which is what makes the presentations defensible, but the dependence is real and worth stating.

This is not a retreat from category theory. `Paths` is left adjoint to the forgetful functor from categories to quivers; the question is only which side of that adjunction carries the comparison. The quiver side is where a tradition's asserted primitives live, and the category side is where their consequences live. The existence half was always a quiver-level fact — every embedding sends Klir's arrow to a generating arrow, never a composite — and had simply been stated more weakly than it was proven.

This document opened with a question: seven traditions, developed independently across six decades, are remarkably compatible. *How?* The answer is $`K \cong \mathbf{2}`. The irreducible categorical content of "system" is a single morphism: *relations depend on things*. Every tradition embeds this arrow. No tradition requires less. Environment, boundary, state, input, output, time, mechanism, feedback — all of it is elaboration of this one structural commitment.

Whether $`\mathbf{2}` can be characterized as a universal construction — a limit, terminal object, or initial algebra — in an appropriate 2-category of shape categories remains open, and the failure of the naive maximality claim makes the question sharper rather than duller. The argument given above is combinatorial and lives in *Quiv*. A categorical characterization would explain *why* the walking arrow is the common core, not merely *that* it is, and would say whether anything survives the passage back across the adjunction into *Cat*. This is a question for 2-category theorists, not a claim this document can discharge.

# Comparison Functors

The shape categories enable precise structural comparison between traditions:

*Mobus → Bunge*: faithful but not full. Every Mobus structural dependency maps to a Bunge dependency, but Mobus has structural commitments (boundary, milieu, capacity) that Bunge does not require. The divergence catalogue is the formal content of what "engineering elaboration" means.

```lean
#check @comparisonFunctor_not_full
```

*Mobus → Myers*: all structural constraints in Mobus map to Myers's `expose` — the observation interface. But Myers's `update` (state transition) has no preimage in Mobus. Mobus captures what systems *are*; Myers captures how they *behave*.

```lean
#check @myers_fiber_input
```

*Wymore → Mobus*: object-injective, but Wymore's `stateOnTime` requires a length-2 path through boundary. Mobus mediates time through interface structure — temporal reasoning is not direct but structurally encoded.

```lean
#check @wymoreToMobusObj_injective
```

*Joslyn → any acyclic tradition*: no comparison functor has been formalized. The cyclic shape generates infinite hom-sets, and a faithful functor from an infinite free category to a finite one cannot exist. The feedback structure that makes Joslyn's framework distinctive is also what makes it categorically incomparable to the others by standard means. Characterizing this incomparability precisely is an open problem. Candidate structures for recovering the comparison include traces on symmetric monoidal categories (which capture feedback as a loop on a process), operads (which formalize composition with typed arities), and double categories with a dedicated feedback morphism dimension. Of these, traces feel closest: a traced monoidal category captures feedback as a loop on a process without requiring the loop to unfold, which matches the afferent-efferent cycle's structure. But traces assume a symmetric monoidal category, and it is not obvious that Joslyn's constraint relation satisfies this. The asymmetry between controller and controlled is load-bearing, not incidental.

The structural traditions share a common core discovered through the commuting triangle. Do the operational traditions share an analogous core? The `myers_update_unreachable` finding — that Mobus has no structural counterpart to Myers's state transition — suggests the operational core may differ from the structural one, encoding dynamics rather than dependency. Whether Mesarovic, Wymore, and Myers converge on a shared operational shape, and whether that shape relates to $`\mathbf{2}` by rotation or extension, is a second open problem.

```lean
#check @myers_update_unreachable
```

A caveat on scope. Shape categories formalize what each tradition *considers structurally relevant* — which components exist and which depend on which. They do not formalize what operations on systems each tradition *supports*. Two Mobus systems cannot compose in this formalization; two Myers systems can (via lens composition), but that structure lives in the category of deterministic systems, not in the shape category. Formalizing the category of systems *within* each tradition — where morphisms are structure-preserving maps and composition is system combination — is the compositional program that complements this comparative one.

# Methodology

This formalization was produced collaboratively between a domain expert and an LLM (Anthropic's Claude) using the Lean 4 proof assistant. The human provided editorial judgment, interpretation choices when source text was ambiguous, and caught cases where LLM output was type-correct but conceptually wrong. The LLM provided Lean syntax fluency, Mathlib API navigation, and tactic proof generation. The compiler had final authority. Zero `sorry`s means every claim is machine-checked.

The most striking pattern: deep theorems proved by trivially simple tactics. Selection composition (Bunge's Theorem 1.2) proves by `rfl`. Emergence decomposes into set operations via `simp`. These are not trivially expected — they confirm that the right mathematical representations make deep conceptual claims definitionally true.
