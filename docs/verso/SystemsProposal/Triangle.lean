import VersoManual
import Systems.Examples.Thermostat
import Systems.Klir.KlirSystem

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Systems
open Systems.Examples

set_option pp.rawOnError true

#doc (Manual) "The Commuting Triangle" =>

The previous chapter presented seven definitions of "system" across three orientations (structural, operational, and cybernetic). Before asking how all seven relate (which requires category theory), we can ask a narrower question using only set theory: how do the three _structural_ traditions relate to each other?

Klir, Bunge, and Mobus share a set-theoretic language of components, relations, and subsets. They also share a documented intellectual lineage. Bunge (1979) read Klir; he cites Klir and Valach (1967) and Klir and Rogers (1977) in his bibliography. Mobus (2022) read Klir; he cites Klir (2001) explicitly. *Neither Bunge nor Mobus references the other.* They developed independently from a shared Klir root, 43 years apart, using different notation, terminology, and motivating examples.

How compatible are they, really? Both claim Klir as ancestor. Both elaborate his $`(T, R)` into richer structures. If you strip away each author's additions and project back down to Klir, do you get the same thing? Or do forty-three years of independent development introduce subtle divergence that only becomes visible under formal scrutiny?

The operational and cybernetic traditions — Mesarovic, Wymore, Myers, Joslyn — require different machinery. Their shapes are not projections of each other but independent dependency quivers that share a common sub-category. That analysis belongs to the next chapter. Here, we stay with sets, projection maps, and a question that can be answered by the type-checker directly.

$$`\text{Mobus} \xrightarrow{\text{toBunge}} \text{Bunge} \xrightarrow{\text{toKlir}} \text{Klir}`

$$`\text{Mobus} \xrightarrow{\quad\text{toKlir}\quad} \text{Klir}`

Two paths. Same destination. The question is whether they arrive at the same place.

# Stripping Away the Additions

To test compatibility, we build projection maps — functions that strip away each author's additions and return to a simpler framework.

**Bunge → Klir** (forget environment):
- $`T := C` — things are the components
- $`R := S` — relation is the structure

```lean
#check @ConcreteSystem.toKlir
```

What is lost: the distinction between inside and outside. Everything Bunge added — environment $`E`, the disjointness constraint, the requirement that bonds cross the boundary — disappears. The room and outsideAir vanish from the description entirely.

**Mobus → Bunge** (forget milieu, capacity, boundary, transforms, history, time scale):
- $`C := C` — components are exact
- $`E := O` — environment is the discrete objects (milieu $`M` discarded)
- $`S := N.\text{toRelation} \cup G.\text{toRelation}` — capacity $`\kappa` discarded

```lean
#check @MobusSystem.toBunge
```

What is lost: six categories of engineering detail. The ambient milieu collapses into nothing. Flow capacities (millivolts, BTUs) become bare pairs. The boundary, transforms, history, and time scale all disappear. Two Mobus thermostats differing only in their control algorithm — bang-bang vs PID — project to the same Bunge triple.

**Mobus → Klir** (forget everything except $`T` and $`R`):

```lean
#check @MobusSystem.toKlir
```

Now the test. We have two paths from Mobus to Klir: the direct projection, and the route through Bunge. If these three structural definitions are truly layers of a single tradition — not three independent inventions that happen to use similar words — both paths should agree.

# The Two Paths Agree

```lean
#check @triangle_commutes
```

They do more than agree. The proof is `rfl` — *reflexivity*, meaning definitional equality. The type-checker confirms the two paths produce identical values without any reasoning, simplification, or rewriting. The two expressions reduce to the same normal form.

This is stronger than expected. Mathematical compatibility usually requires a proof — an argument that two constructions produce isomorphic results. Here, the compiler confirms identity without reasoning. The two paths are the same *computation*.

Why? The clean projection is not evidence of influence — Bunge did not build on Klir's (T, R) definition. He arrived at sets and relations through an entirely different route: ontological analysis of what it means for concrete things to exist and interact. His partition of the carrier set into composition (C) and environment (E) is philosophically fundamental to his program. But mathematically, $`C \cup E` *is* $`T`, and $`S` *is* $`R`. The projection map just undoes the partition. Bunge's ontological distinction between inside and outside adds no new relational structure — environment is a labeling choice, not a structural one.

The convergence is not coincidence. The mathematical design space for "things and their connections" in set theory is small enough that independent investigators working from different motivations — Klir from epistemology, Bunge from ontology, Mobus from engineering methodology — arrive at the same types. The formalization made that invisible agreement visible.

# What Gets Lost Along the Way

But agreement at the bottom does not mean equivalence at the top. The projection maps that produce the `rfl` are lossy — many Mobus 8-tuples map to the same Bunge triple. Understanding what each layer adds means understanding what each projection discards. Six categories of information in Mobus have no Bunge counterpart:

- **Milieu** $`M` — Ambient conditions (temperature, pressure). Bunge's $`E` is a set of things only.
- **Capacity** $`\kappa` — How much flows (BTUs, bits, dollars). Bunge's $`S` is pairs, not weighted.
- **Boundary properties** $`\pi` — Permeability, insulation. Bunge has no boundary concept.
- **Transforms** $`\tau` — What things *do* to their inputs. No functional component in Bunge.
- **History** $`\eta` — Accumulated knowledge. No memory component in Bunge.
- **Time scale** $`\delta` — Temporal resolution. Time-indexed but unformalized in Bunge.

Two Mobus systems differing only in these six categories project to the **same** Bunge CES triple. This is *independent convergence with formally characterized divergence*.

To see what each step of abstraction discards concretely, consider the thermostat:

- **Milieu** $`M` — ambient temperature, humidity. The disturbance source that control₂ requires.
- **Capacity** $`\kappa` — BTUs, millivolts, on/off. Magnitude of flows, invisible to Bunge.
- **Boundary** $`\pi` — thermal insulation R-value. How much disturbance penetrates.
- **Transforms** $`\tau` — the if/then control rule. The semantic relation, the rule, the sign.
- **History** $`\eta` — recent temperature readings. Memory — PID needs the integral term.
- **Time scale** $`\delta` — 30-second polling interval. Can the system track fast disturbances?

**Mobus → Bunge.** Milieu $`M` disappears (ambient temperature and humidity vanish). Capacity labels disappear (the distinction between a temperature signal, a binary command, and a heat-energy flow is collapsed — all become bare pairs). Boundary properties, transforms, history, and time scale disappear. Two Mobus thermostats differing only in their control algorithm — bang-bang vs PID — project to the **same** Bunge CES triple. They are structurally identical. They differ only in what the controller *does*.

**Bunge → Klir.** Environment $`E` disappears. The distinction between "inside" and "outside" is lost — and something strange happens. Room becomes a *phantom entity*: present in the relational structure ($`R` contains pairs referencing it) but not counted among the system's things ($`T`). The thermostat still acts on the room; Klir's formalism just cannot say that the room is *outside*. outsideAir disappears entirely — it has no bonds, so it leaves no trace in $`R`. This is the formal content of what Bunge's environment concept buys you — and what you lose without it.

# Surprises from the Compiler

The commuting triangle was the planned result. But the formalization process also corrected and extended the source texts in ways we did not expect.

**The type of S.** Joslyn asked: *"S is a set of sets of tuples, right?"* Yes. This is the Bunge-side analogue of the formalization choice noted in the previous chapter for Klir's $`T` — there, we committed to a single set rather than a family; here, the same question arises for Bunge's $`S`. The formalization proves it doesn't matter for the theorems. Take the family of relations, extract the internal part of each, then union — same result as first flattening everything, then extracting internals. The flat encoding is a faithful quotient.

**Boundary completeness — derived, not axiomatized.** The systems-theoretic property that "all interaction is mediated by the boundary" is not assumed. It *follows structurally* from the bipartite constraint on external flows. Mobus's five coherence constraints from the previous chapter are doing more work than they appear to.

# How Clean Is Too Clean?

These surprises strengthen the story — but they also raise a question about its foundations. The `rfl` is clean. Perhaps too clean. How much of that tidiness comes from the mathematics and how much from our formalization choices? Consider two readings of Bunge's "structure":

1. *Flat reading*: structure is `Set (α × α)` — a single relation. This is what `ConcreteSystem` uses.
2. *Family reading*: structure is `Set (Set (α × α))` — a "set of relations" (Bunge's plural). This is what `RichConcreteSystem` implements.

Under the family reading, the Mobus → Rich Bunge projection creates a 2-element structure family: \{N.toRelation, G.toRelation\} — preserving the internal/external distinction. The Rich → Klir projection must flatten this family via set union to produce a single relation R. The triangle still commutes, but the proof changes from `rfl` (definitional equality) to `simp` with the lemma `Set.sUnion_pair` (semantic equality — the checker needs a lemma to see it).

The difference matters: `rfl` works only because the flat representation hides an information-loss step that the family version makes explicit. To reach Klir's (T, R), you must forget not just environment but the *organization* of relations — which bonds are internal and which cross the boundary. Both versions produce valid proofs. The compatibility does not depend on a particular reading of Bunge.

The commuting triangle establishes that three traditions agree when projected to their common root. But the title promises seven. The remaining four — Myers, Wymore, Mesarovic, and Joslyn — require categorical rather than set-theoretic language, and one of them (Joslyn's cyclic feedback structure) is unlike anything in the first three. The next chapter asks: what happens when you encode all seven as shape categories and look for what they share?

