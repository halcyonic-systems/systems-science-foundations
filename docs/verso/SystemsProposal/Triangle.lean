import VersoManual
import Systems.Examples.Thermostat
import Systems.Klir.KlirSystem

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Systems
open Systems.Examples

set_option pp.rawOnError true

#doc (Manual) "The Commuting Triangle" =>

Bunge (1979) read Klir — he cites Klir and Valach (1967) and Klir and Rogers (1977) in his bibliography. Mobus (2022) read Klir — he cites Klir (2001) explicitly. **Neither Bunge nor Mobus references the other.** They developed independently from a shared Klir root, 43 years apart, using different notation, terminology, and motivating examples.

The formalization discovers that both paths from Mobus's 8-tuple back to Klir's $`(T, R)` — via Bunge or directly — produce the same result. Not merely the same up to isomorphism. *Definitionally identical.*

# The Projection Maps

**Bunge → Klir** (forget environment):
- $`T := C` — things are the components
- $`R := S` — relation is the structure

```lean
#check @ConcreteSystem.toKlir
```

**Mobus → Bunge** (forget milieu, capacity, boundary, transforms, history, time scale):
- $`C := C` — components are exact
- $`E := O` — environment is the discrete objects (milieu $`M` discarded)
- $`S := N.\text{toRelation} \cup G.\text{toRelation}` — capacity $`\kappa` discarded

```lean
#check @MobusSystem.toBunge
```

**Mobus → Klir** (forget everything except $`T` and $`R`):

```lean
#check @MobusSystem.toKlir
```

# The Theorem

```lean
#check @triangle_commutes
```

The proof is `rfl` — *reflexivity*. The Lean type-checker confirms that the two paths produce not just equal but definitionally identical `KlirSystem` values. No proof search, no simplification, no rewriting. The two expressions reduce to the same normal form.

This traces to both Bunge and Mobus inheriting $`T` = `Set α` and $`R` = `Set (α × α)` from Klir without changing the mathematical type. Neither author knew this about the other's work. It was *discovered* through formalization.

# Information Loss

The bridge is a projection: many Mobus 8-tuples map to the same Bunge triple. Six categories of information have no Bunge counterpart:

- **Milieu** $`M` — Ambient conditions (temperature, pressure). Bunge's $`E` is a set of things only.
- **Capacity** $`\kappa` — How much flows (BTUs, bits, dollars). Bunge's $`S` is pairs, not weighted.
- **Boundary properties** $`\pi` — Permeability, insulation. Bunge has no boundary concept.
- **Transforms** $`\tau` — What things *do* to their inputs. No functional component in Bunge.
- **History** $`\eta` — Accumulated knowledge. No memory component in Bunge.
- **Time scale** $`\delta` — Temporal resolution. Time-indexed but unformalized in Bunge.

Two Mobus systems differing only in these six categories project to the **same** Bunge CES triple. This is *independent convergence with formally characterized divergence*.

# What the Compiler Found

Beyond the commuting triangle itself, the formalization process corrected and extended the source texts.

**The type of S.** Joslyn asked: *"S is a set of sets of tuples, right?"* Yes. But the formalization proves it doesn't matter for the theorems. Take the family of relations, extract the internal part of each, then union — same result as first flattening everything, then extracting internals. The flat encoding is a faithful quotient.

**Boundary completeness — derived, not axiomatized.** The systems-theoretic property that "all interaction is mediated by the boundary" is not assumed. It *follows structurally* from the bipartite constraint on external flows.

# Convergence and Choice

The `rfl` is clean — perhaps too clean. It depends on a formalization choice. Consider two readings of Bunge's "structure":

1. *Flat reading*: structure is `Set (α × α)` — a single relation. This is what `ConcreteSystem` uses.
2. *Family reading*: structure is `Set (Set (α × α))` — a "set of relations" (Bunge's plural). This is what `RichConcreteSystem` implements.

Under the family reading, the Mobus → Rich Bunge projection creates a 2-element structure family: \{N.toRelation, G.toRelation\} — preserving the internal/external distinction. The Rich → Klir projection must flatten this family via set union to produce a single relation R. The triangle still commutes, but the proof is no longer `rfl` — it requires `simp` with the lemma `Set.sUnion_pair`.

The gap between `rfl` and `simp`:

- `rfl` — *syntactic identity*. The two expressions are the same computation; the type-checker confirms without reasoning.
- `simp` — *semantic equality*. The expressions compute to equal values, but the checker needs a lemma to see it.

Both are true. But `rfl` works only because the flat representation hides an information-loss step that the family version makes explicit: to reach Klir's (T, R), you must forget not just environment but the *organization* of relations — which bonds are internal and which cross the boundary.

What matters is that *both* versions produce valid proofs. The compatibility does not depend on a particular reading of Bunge. When three independent researchers arrive at structures that compose cleanly under multiple formalizations, that is evidence the decomposition reflects something real about systemhood, not about formalization choices.

# Emergence, Briefly

Philosophical debates about emergence can span hundreds of pages. The formal definition reduces to set operations:

- *emergentProperties* = after ∖ before (properties that appear)
- *lostProperties* = before ∖ after (properties that disappear)
- *qualitativeNovelty* = lost ∪ emergent = symmetric difference

`simp` closes it. Bunge's Definition 1.13 on emergence, once formalized, is a one-liner.
