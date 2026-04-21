import VersoManual
import Systems.Category.CommonCore
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

The commuting triangle tells us the three frameworks agree when projected to their common root. But what about the *structure of the relationships themselves*? Category theory gives us the vocabulary to ask: when we say "Mobus refines Bunge," what *kind* of refinement is it? What is preserved, and what is forgotten?

# The Ordering Triangle

There are three natural ways to order systems by their subsystem relationships, depending on how much structure you track. The *family ordering* (tracking individual relations like N and G separately), the *refinement ordering* (requiring only that each relation has a coarsening), and the *flat ordering* (using only the union of all relations). Each defines a thin category. The forgetful functors between them are *faithful* (they don't create spurious relationships) but *not full* (they lose distinctions).

```lean
#check @instFaithfulForgetFamily
#check @not_full_forgetFamily
```

The non-fullness results are constructive: explicit witnesses on `Fin 2` (systems with just two elements) show that a refinement-subsystem pair need not be a family-subsystem pair, and a flat-subsystem pair need not be a refinement-subsystem pair. The choice of structure representation *determines which subsystem ordering you get* — different readers of these frameworks are implicitly working in different categories.

# Bridge Factorization

The Mobus-to-Bunge bridge factors through the structure family representation. Mobus's separation of internal network (N) and external flows (G) *is* the natural two-element structure family. The bridge was always performing a flattening — the categorical language makes this visible:

`toBunge = toRichBunge ⋙ flatten`

```lean
#check @bridge_factors_functor
```

This factorization is a theorem about the *relationship between frameworks* that neither Bunge nor Mobus stated. The extended diagram commutes: the factorization composes with the bridge to Klir, extending the original commuting triangle through the intermediate structure family.

# Shape Categories and the Common Core

Each tradition's definition of "system" can be encoded as a *shape category* — a free category on the dependency quiver of its components. The shape captures what a tradition considers structurally relevant: which components exist and which depend on which.

Seven traditions yield seven shapes:

- $`I_{Klir}` — 2 objects, 1 arrow: the walking arrow *T → R* (things determine relations)
- $`I_{Bunge}` — 3 objects, 3 arrows: the CES dependency quiver
- $`I_{Mobus}` — 8 objects, 5 arrows + 3 isolated: the full 8-tuple structure
- $`I_{Myers}` — 3 objects, 2 arrows: the lens/deterministic system pattern
- $`I_{Wymore}` — 4 objects, 3 arrows: the FSD quintuple with time
- $`I_{Mesarovic}` — 2-3 objects: the input/output base
- $`I_{Joslyn}` — 3 objects, 3 arrows: the cyclic feedback loop

The common core theorem proves that Klir's walking arrow $`\mathbf{2}` embeds faithfully into all seven shapes:

```lean
#check @klirToBunge
```

The irreducible categorical content of "system" across 60 years of independent traditions is a single morphism: *relations depend on things*. Everything else — environment, boundary, state, input, output, time, mechanism, feedback — is tradition-specific elaboration of this seed.

# Comparison Functors

The shape categories enable precise structural comparison between traditions:

*Mobus → Bunge*: faithful but not full. Every Mobus structural dependency maps to a Bunge dependency, but Mobus has structural commitments (boundary, milieu, capacity) that Bunge does not require. The divergence catalogue is the formal content of what "engineering elaboration" means.

```lean
#check @comparisonFunctor_not_full
```

*Mobus → Myers*: all structural constraints in Mobus map to Myers's `expose` — the observation interface. But Myers's `update` (state transition) has no preimage in Mobus. Mobus captures what systems *are*; Myers captures how they *behave*.

*Wymore → Mobus*: object-injective, but Wymore's `stateOnTime` requires a length-2 path through boundary. Mobus mediates time through interface structure — temporal reasoning is not direct but structurally encoded.

# The Bitcoin Application

The categorical tools developed for systems ontology have an immediate application in a companion formalization: modeling the relationship between Bitcoin's UTXO ledger and Ethereum's account-based ledger as a functor between categories.

The *collapse functor* maps UTXO states to their balance equivalents. It is:

- *Essentially surjective* — every balance map has a UTXO preimage
- *Not faithful* — two distinct UTXO operations (consuming and reproducing different UTXOs with the same total value) are distinguishable in UTXO-land but invisible at the balance level

The non-faithfulness is the first genuinely new result requiring categories — it is not statable without `Category` instances, since it requires injectivity on hom-sets. The interpretation: UTXO-land has strictly more transactional information than account-land. The collapse functor makes this precise. It is a formal answer to "what does Bitcoin track that Ethereum doesn't?" — the individual identity of value units.

# Correcting Bunge on Algebraic Structure

Bunge §1.6 states: "the set of all systems has no algebraic structure — not even the rather modest one of a semigroup." He's right about semigroups — not every pair of systems can compose. But the partiality of composition *is* the structure, not the absence of it.

Two systems compose when their boundaries match: a producer's output leg glues to a consumer's input leg along a shared species. The patterns of which systems can compose with which — the "shapes" of legal compositions — form an operad. Systems are an operad algebra: they carry structure richer than a semigroup, precisely because composition is typed by boundary compatibility rather than universally defined.

This is a genuine correction to a foundational text — Bunge diagnosed the right intuition (systems don't compose freely) but drew the wrong conclusion (therefore no algebraic structure exists).

# Methodology

This formalization was produced collaboratively between a domain expert and an LLM (Anthropic's Claude) using the Lean 4 proof assistant. The human provided editorial judgment, interpretation choices when source text was ambiguous, and caught cases where LLM output was type-correct but conceptually wrong. The LLM provided Lean syntax fluency, Mathlib API navigation, and tactic proof generation. The compiler had final authority — zero `sorry`s means every claim is machine-checked.

The most striking pattern: deep theorems proved by trivially simple tactics. Selection composition (Bunge's Theorem 1.2) proves by `rfl`. Emergence decomposes into set operations via `simp`. These are not trivially expected — they confirm that the right mathematical representations make deep conceptual claims definitionally true.
