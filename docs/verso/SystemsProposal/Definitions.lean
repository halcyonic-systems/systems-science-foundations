import VersoManual
import Systems.Examples.Thermostat
import Systems.Klir.KlirSystem

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Systems
open Systems.Examples

set_option pp.rawOnError true

#doc (Manual) "Three Definitions, One Tradition" =>

The general systems tradition contains several set-theoretic definitions of "system." They are not competing alternatives but *layers* of increasing ontological commitment. We present three — Klir, Bunge, and Mobus — each in its formal definition, with proper citations and the Lean 4 encoding.

# Klir: S = (T, R)

$$`S = (T, R)`

> A system $`S` is an ordered pair $`S = (T, R)`, where $`T` is a set of things (*thinghood*) and $`R` is a relation on $`T` (*systemhood*).
>
> — Klir, *Facets of Systems Science*, 2001, Eq. 1.1

A thing becomes a system when you specify which of its parts are related. This is the simplest formal definition of system in the general systems tradition — and, as we will prove, the common mathematical ancestor of both Bunge and Mobus.

```lean
#check @KlirSystem
```

The type is transparent: `things` is a set over an arbitrary carrier type `α`, and `relation` is a set of ordered pairs. No time, no state, no environment, no boundary. Just $`T` and $`R`.

```lean
example : KlirSystem Nat := ⟨{1, 2, 3}, {(1, 2), (2, 3)}⟩
```

Three natural numbers, two ordered pairs. That is a system in Klir's sense. Everything else the systems tradition adds — environment, flows, boundaries, transforms — is elaboration on this seed.

The definition looks trivially simple, but Klir (Ch. 2) emphasizes that T and R are "extremely rich in content." T can be a single set or a family of distinct sets; when T is a family, R becomes a relation on their product. The formalization commits to a specific reading: T is a single set (`Set α`), R is a binary relation (`Set (α × α)`). This is the natural base case — it captures the structure common to all three frameworks. Richer relational forms would require dependent types. The current choice keeps the types simple enough that projection maps compose by `rfl`.

**The thermostat as a Klir system.** Three things (thermometer, controller, furnace) and four ordered pairs (room acts on thermometer, thermometer acts on controller, controller acts on furnace, furnace acts on room). The relation captures *that* things interact, not *how* or *what kind*.

# Bunge: ⟨C, E, S⟩

$$`\sigma = \langle C(\sigma), E(\sigma), S(\sigma) \rangle`

> Let $`T` be a nonempty set. Then the ordered triple $`\sigma = \langle C, E, S \rangle` is (or represents) a system over $`T` iff $`C` and $`E` are mutually disjoint subsets of $`T` (i.e. $`C \cap E = \emptyset`), and $`S` is a nonempty set of relations on the union of $`C` and $`E`.
>
> — Bunge, *Treatise on Basic Philosophy* Vol. 4, 1979, Ch. 1

Bunge adds one primitive that Klir lacks: *environment*. A system exists *within* something, and that something is a first-class component of its description. Where Klir asks "what are the parts and how are they related?", Bunge asks "what is inside, what is outside, and how do they interact?"

Three coherence constraints, enforced at the type level:

1. $`C \cap E = \emptyset` — components and environment do not overlap
2. All relations in $`S` are defined on $`C \cup E` — no dangling references
3. At least two distinct components are bonded — otherwise it is a heap, not a system

```lean
#check @ConcreteSystem
```

The `ActsOn` typeclass provides Bunge's action relation — `a ▷ b` means "a modifies b's trajectory." This is the primitive notion of bonding: causal influence between concrete things.

**A 47-year-old error.** Bunge's Definition 1.6 states that the subsystem relation is *"reflexive, asymmetric, and transitive."* No relation can be both reflexive and asymmetric. Reflexivity gives $`x \leq x` for all $`x`; asymmetry requires $`x \leq y \implies \neg(y \leq x)` — substituting $`y = x` yields a contradiction. The compiler rejected the asymmetry claim. The correct property is **antisymmetry**: $`\sigma_1 \leq \sigma_2` and $`\sigma_2 \leq \sigma_1` implies their CES triples are equal. This error has been in print since 1979.

**Note on CESM.** Later work (Bunge, *Systemism*, 2000) extends the triple to $`\langle C, E, S, M \rangle` adding mechanism. The 1979 *Treatise* uses the triple. The formalization encodes the 1979 definition; mechanism enters through Mobus's transforms $`\tau`.

**The thermostat as a Bunge system.** Composition $`C` = \{thermometer, controller, furnace\}. Environment $`E` = \{room, outsideAir\}. Structure $`S` = the four causal bonds. A modeling decision: the room is environment because the thermostat acts *on* the room — the room is what the system is trying to regulate.

# Mobus: The 8-Tuple

$$`S_{i,l} = \langle C, N, E, G, B, T, H, \Delta t \rangle_{i,l}`

Mobus elaborates Klir in a different direction from Bunge — toward engineering methodology. Where Bunge asks "what *is* a system?", Mobus asks "how do you *describe* one?" He cites Klir (2001) explicitly: *"The development of this approach was inspired originally by Klir (2001)"* (Ch. 4, p. 14).

The 8-tuple fields:

- $`C` — **Components**: the set of entities at level $`l`
- $`N = \langle C, L \rangle` — **Internal network**: directed flow graph among components, with capacity labels $`\kappa`
- $`E = \langle O, M \rangle` — **Environment**: discrete objects $`O` plus an opaque *milieu* $`M`
- $`G` — **External flows**: bipartite graph between $`O` and interface components
- $`B = \langle P, I \rangle` — **Boundary**: properties $`P` plus interface components $`I \subseteq C`
- $`T` — **Transforms**: domain-specific processing functions
- $`H` — **History**: stored knowledge / memory
- $`\Delta t` — **Time scale**: temporal resolution

```lean
#check @MobusSystem
```

Seven type parameters. Five coherence constraints enforced by the compiler:

1. Internal network nodes $`=` components
2. $`C \cap O = \emptyset` — disjointness (inherited from Bunge)
3. $`I \subseteq C` — interfaces are components
4. External flows are *bipartite* between $`O` and $`I`
5. External flow nodes $`\subseteq O \cup I`

The bipartite constraint alone *implies* boundary completeness: all interaction between system and environment passes through the boundary. This is derived, not axiomatized.

The first five fields ($`C, N, E, G, B`) are structurally active — they participate in proofs. The last three ($`T, H, \Delta t`) are parametric — carried data with no structural role in the ontology. This is by design: transforms are domain-specific, history is implementation-specific, and time scale is observational. The ontology captures *what a system has*, not *what it does*. That distinction will matter.

**The thermostat as a Mobus system.** Everything from Bunge, plus: internal flows have capacity labels (millivolts from thermometer, binary commands from controller, BTUs from furnace). The boundary identifies thermometer and furnace as interface components. outsideAir enters through the milieu $`M` — ambient thermal effects, not a point-source flow. Transforms $`\tau` = `Unit` — we have no formal theory of what the controller *does*. That absence is the gap this document is building toward.

```lean
#check thermostatMobus
```
