import VersoManual
import Systems.Examples.Thermostat
import Systems.Klir.KlirSystem

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Systems
open Systems.Examples

set_option pp.rawOnError true

#doc (Manual) "A Formal Systems Ontology and Its Open Frontier" =>

%%%
authors := ["Shingai Thornton"]
%%%

*Klir, Bunge, and Mobus — and the layer that needs your framework.*

In summer 2025 I wrote an independent study paper to illustrate the kind of work I wanted to do in systems ontology — bringing Bunge-style philosophical rigor to Mobus's framework in service of developing System Language. You called it a down-payment and gave me thirty red-text comments marking the areas to be addressed. I framed Mobus's 8-tuple as a "systematic extension" of Bunge's CES triple. Then you asked the right question: *does Mobus actually cite Bunge?* I checked. He doesn't. Neither references the other.

That killed the "extension" framing and opened the real question: _how are two independently developed frameworks this compatible?_ The answer turned out to be Klir. Both cite him. Both inherit $`T` = `Set α` and $`R` = `Set (α × α)` from his $`(T, R)` definition without changing the mathematical type. The formalization proves this — the commuting triangle is `rfl`.

Thirteen of your red-text comments mapped directly to machine-checked code. Your question about the type of $`S` — *"S is a set of sets of tuples, right?"* — forced a design decision the Lean compiler settled in 146 lines and two theorems.

Now that the thesis is defended, this is the work I want to focus on. This document presents what the formalization produced, and where it reaches its limits — limits that your variety-theoretic and semiotic framework is precisely designed to resolve.

Every definition below is rendered three ways: typeset mathematics, English prose, and live Lean code. Hover over any Lean expression to see its type. The compiler has checked all of it.

# Three Definitions, One Tradition

The general systems tradition contains several set-theoretic definitions of "system." They are not competing alternatives but *layers* of increasing ontological commitment. We present three — Klir, Bunge, and Mobus — each in its formal definition, with proper citations and the Lean 4 encoding.

## Klir: S = (T, R)

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

**The thermostat as a Klir system.** Three things (thermometer, controller, furnace) and four ordered pairs (room acts on thermometer, thermometer acts on controller, controller acts on furnace, furnace acts on room). The relation captures *that* things interact, not *how* or *what kind*.

## Bunge: ⟨C, E, S⟩

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

## Mobus: The 8-Tuple

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

# The Commuting Triangle

Bunge (1979) read Klir — he cites Klir and Valach (1967) and Klir and Rogers (1977) in his bibliography. Mobus (2022) read Klir — he cites Klir (2001) explicitly. **Neither Bunge nor Mobus references the other.** They developed independently from a shared Klir root, 43 years apart, using different notation, terminology, and motivating examples.

The formalization discovers that both paths from Mobus's 8-tuple back to Klir's $`(T, R)` — via Bunge or directly — produce the same result. Not merely the same up to isomorphism. *Definitionally identical.*

## The Projection Maps

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

## The Theorem

```lean
#check @triangle_commutes
```

The proof is `rfl` — *reflexivity*. The Lean type-checker confirms that the two paths produce not just equal but definitionally identical `KlirSystem` values. No proof search, no simplification, no rewriting. The two expressions reduce to the same normal form.

This traces to both Bunge and Mobus inheriting $`T` = `Set α` and $`R` = `Set (α × α)` from Klir without changing the mathematical type. Neither author knew this about the other's work. It was *discovered* through formalization.

## Information Loss

The bridge is a projection: many Mobus 8-tuples map to the same Bunge triple. Six categories of information have no Bunge counterpart:

- **Milieu** $`M` — Ambient conditions (temperature, pressure). Bunge's $`E` is a set of things only.
- **Capacity** $`\kappa` — How much flows (BTUs, bits, dollars). Bunge's $`S` is pairs, not weighted.
- **Boundary properties** $`\pi` — Permeability, insulation. Bunge has no boundary concept.
- **Transforms** $`\tau` — What things *do* to their inputs. No functional component in Bunge.
- **History** $`\eta` — Accumulated knowledge. No memory component in Bunge.
- **Time scale** $`\delta` — Temporal resolution. Time-indexed but unformalized in Bunge.

Two Mobus systems differing only in these six categories project to the **same** Bunge CES triple. This is *independent convergence with formally characterized divergence*.

# The Thermostat — Your Example, Three Frameworks

You used the thermostat in the 1995 paper to derive the internal-state requirement (Proposition 29) and the semantic-relation argument. Here it is formalized under all three frameworks. 160 lines of Lean, zero `sorry`s.

## Entities and Action

Five entities. Four causal bonds.

```lean
#check Entity
#check entityActsOn
```

A modeling decision: outsideAir does not act on anything discretely — its thermal effect enters through the milieu $`M`, not a point-source flow. This is the engineering judgment Mobus's $`E = \langle O, M \rangle` decomposition makes possible and Bunge's flat $`E` does not.

## Building the Mobus System

The historical direction is Klir → Bunge → Mobus: increasing elaboration over 43 years. The formal direction is the reverse: Mobus → Bunge → Klir, increasing abstraction through projection. We follow the formal direction because it reveals the convergence — and because it preserves what the history obscures. Building *up* from Klir would suggest Mobus extends Bunge, which is exactly the "systematic extension" framing your question killed. Mobus never read Bunge. Building *down* from Mobus lets each framework stand independently, and the projections show where they meet without implying one derives from the other. The information loss table below shows exactly what each step of abstraction discards.

We build the Mobus system first — it carries the most information — then derive the others by projection.

```lean
#check thermostatMobus
```

The parametric fields are telling: transforms = `Unit`, history = `Unit`, timeScale = `Unit`. We have a structural skeleton but no theory of what the controller *does*, what it *remembers*, or *how fast* it operates.

## Bunge and Klir — By Projection

Rather than defining independently, we *extract* them from the Mobus 8-tuple via the projection maps:

```lean
#check thermostatBunge
#check thermostatKlir
```

A structural observation: **room appears in the relation but not in the thing-set.** After the Bunge → Klir projection, the pairs (room, thermometer) and (furnace, room) are in $`R`, but room $`\notin T`. Room becomes a *phantom entity* — present in the system's relational structure but not counted among its things. This is the formal content of losing the environment component $`E`.

## The Triangle on This Instance

```lean
#check thermostat_triangle_commutes
```

`rfl`. Both paths from the Mobus thermostat to the Klir system produce definitionally identical values.

**What was lost at each step:**

**Mobus → Bunge.** Milieu $`M` disappears (ambient temperature and humidity vanish). Capacity labels disappear (the distinction between a temperature signal, a binary command, and a heat-energy flow is collapsed — all become bare pairs). Boundary properties, transforms, history, and time scale disappear.

**Bunge → Klir.** Environment $`E` disappears. The distinction between "inside" and "outside" is lost. Room becomes a phantom in $`R`; outsideAir disappears entirely (it has no bonds).

**But all three descriptions miss the same thing.** The controller's logic — *if temperature < setpoint then turn on furnace* — is a *rule*, not a law. It was selected from a variety of possible control functions. It could have been a PID controller, a bang-bang controller, or a machine-learning policy. Two Mobus thermostats differing only in transforms — one with bang-bang control, one with PID — project to the **same** Bunge CES triple. They are structurally identical. They differ only in what the controller *does*.

This is precisely your point from the 1995 paper: the feedback function $`f : O_i \to O_e` *must be a rule (contingent entailment), not a natural law*. Rules are arbitrary, conventional, and selected — exactly the properties of Peircean signs. The formalization reaches its limit here.

# The Open Frontier

## What the Formalization Cannot Yet Express

**Variety.** The current formalization has no concept of $`|X|`, $`|S|`, or $`C = X - S` as a measure of constraint. Your Definitions 13, 17, 18 — dimensional variety (the number of distinct dimensions $`n`), cardinal variety (the cardinality $`|S|` bounded by $`1 \leq |S| \leq |X|`), and constraint as set subtraction — provide the measure-theoretic layer that the structural ontology lacks.

$$`S_1 \subseteq X_1 \times \cdots \times X_n, \quad C := X - S`

**The rule/law distinction.** The `ActsOn` typeclass is opaque — a `Prop`-valued binary relation. It does not distinguish between a natural law (the ball rolls downhill) and a rule (the controller turns on the furnace). Your distinction between laws and rules (1995, §4.2) is precisely what `ActsOn` collapses.

**Control₂.** The formalization can represent that the controller acts on the furnace. It cannot express *active maintenance of a dynamic equilibrium against environmental disturbance* — your Definition 28. This requires temporal reasoning and second-order constraint that the snapshot model does not support.

The Lean column is deliberately empty here. This is the gap the formalization identifies but cannot fill alone.

## What Your Framework Provides

**Dimensional and cardinal variety give the 8-tuple a measure.** Mobus's component set $`C` has dimensional variety $`n = |C|`. His capacity $`\kappa` is a cardinal variety measure on edges. Your two-axis framework (dimensional $`\times` cardinal) provides the quantitative layer.

**The constraint $`C = X - S` connects directly to Bunge's structure.** Your System₁ constraint is the complement of the system relation within the full product space. Formalizing this gives the Bunge/Mobus framework a measure of *how constrained the system is*.

**The semantic layer gives Mobus's transforms internal structure.** The transforms $`\tau` are the natural home for contingent entailments. But $`\tau` is currently parametric — an opaque type with no internal theory. Your semiotic framework provides the theory:
- $`\tau` as a *law* (necessary entailment, discovered) — gravitational acceleration
- $`\tau` as a *rule* (contingent entailment, selected from a variety) — the controller's if/then logic
- $`\tau` as a *code* (arbitrary, conventional, interpretable) — a sensor reading mapped to a command

This is the classification that makes "too hot" → "turn off furnace" a *sign*, not just a function.

## The Categorification Question

Two complementary approaches to categorical systems theory exist:

**The combinatorial approach** (your 2018 work with Purvine): start with hypergraphs, find the right category to house them. Hypergraphs generalize binary relations to $`n`-ary — exactly the step from Klir's ordered pairs to Mesarovic's full product $`\prod X_i`.

**The foundational approach** (this formalization): start from categorical principles — lenses, functors — and derive what systems must be for composition to work. The bridge factorization (Mobus → RichBunge → Bunge = Mobus → Bunge) is already a functor triangle.

The combinatorial side asks "what is the right category for my objects?" The foundational side asks "what must objects be for composition to work?" Neither is complete without the other.

## Where the Tree Grows

The formal ontology is not the endpoint — it is the foundation for *System Language (SL)*, a formally specified, computationally executable language for systems science, implemented in BERT. The coherence constraints Lean enforces — disjointness, bipartiteness, boundary completeness — are exactly the grammar rules SL compiles from. The tree is the formal specification.

Your variety-theoretic and semiotic framework would give SL something no systems language has ever had: a formal account of *what kind of functional relation* inhabits a system — rule or law — and what that distinction implies about meaning, control, and autonomy.

The tree does not end here. It opens.
