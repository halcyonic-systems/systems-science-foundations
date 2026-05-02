import VersoManual
import Systems.Examples.Thermostat
import Systems.Klir.KlirSystem
import Systems.Category.ShapeMesarovic
import Systems.Category.ShapeMyers
import Systems.Category.ShapeWymore
import Systems.Category.ShapeJoslyn
import Systems.Category.ShapeComparison_Myers
import Systems.Category.ShapeComparison_Wymore
import Systems.Category.CommonCore

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Systems
open Systems.Examples

set_option pp.rawOnError true

#doc (Manual) "Seven Definitions, One Tradition" =>

The general systems tradition contains several set-theoretic definitions of "system." They are not competing alternatives but *layers* of commitment: to different ontological primitives, different mathematical machinery, and different answers to the question "what matters most about a system?" We present seven, developed independently across six decades, each in its formal definition with proper citations and the Lean 4 encoding.

The first three (Klir, Bunge, and Mobus) are *structural*. Their arrows point inward: relations depend on things, structure depends on composition, networks depend on components. The next three (Mesarovic, Wymore, and Myers) are *operational*. Their arrows point outward: state determines what you can observe, what happens next, how subsystems compose. The seventh (Joslyn) is *cybernetic*. Its arrows form a cycle: feedback, constraint, and the semantics of control.

# Klir: S = (T, R)

$$`S = (T, R)`

> A system $`S` is an ordered pair $`S = (T, R)`, where $`T` is a set of things (*thinghood*) and $`R` is a relation on $`T` (*systemhood*).
>
> — Klir, *Facets of Systems Science*, 2001, Eq. 1.1

The two components:

- $`T` — **Things**: the raw material, the parts that exist before any relationship is asserted (*thinghood*)
- $`R \subseteq T \times T` — **Relation**: which of those things are related (*systemhood*)

A thing becomes a system when you specify which of its parts are related. This is the simplest formal definition of system in the general systems tradition, and, as we will prove, the common mathematical ancestor of both Bunge and Mobus.

```lean
#check @KlirSystem
```

No time, no state, no environment, no boundary. Just $`T` and $`R`.

```lean
example : KlirSystem Nat := ⟨{1, 2, 3}, {(1, 2), (2, 3)}⟩
```

Three natural numbers, two ordered pairs. That is a system in Klir's sense. Everything else the systems tradition adds (environment, flows, boundaries, transforms) is elaboration on this seed.

The definition looks trivially simple, but Klir (Ch. 2) emphasizes that $`T` and $`R` are "extremely rich in content." $`T` can be a single set or a family of distinct sets; when $`T` is a family, $`R` becomes a relation on their product.

**Formalization choice.** We commit to the base case: $`T` is a single set (`Set α`), $`R` is a binary relation (`Set (α × α)`). This captures the structure common to all three frameworks without requiring dependent types. The payoff: projection maps compose by `rfl` — a fact that would be obscured by a richer encoding. Similarly, Klir allows $`R` to be an n-ary relation; the formalization restricts to binary pairs. Both choices — single carrier, binary relation — are the minimal base case. Richer arities would require dependent types without changing the structural comparison results.

**The thermostat as a Klir system.**

$$`T = \{\text{thermometer}, \text{controller}, \text{furnace}\}`

$$`R = \{(\text{room}, \text{thermometer}), (\text{thermometer}, \text{controller}), (\text{controller}, \text{furnace}), (\text{furnace}, \text{room})\}`

The relation captures *that* things interact, not *how* or *what kind*. Note that $`(\text{room}, \text{thermometer}) \in R` is the same assertion that Bunge will write as $`\text{room} \triangleright \text{thermometer}` — ordered-pair membership and the action relation are two notations for the same fact.

# Bunge: ⟨C, E, S⟩

$$`\sigma = \langle C(\sigma), E(\sigma), S(\sigma) \rangle`

> Let $`T` be a nonempty set. Then the ordered triple $`\sigma = \langle C, E, S \rangle` is (or represents) a system over $`T` iff $`C` and $`E` are mutually disjoint subsets of $`T` (i.e. $`C \cap E = \emptyset`), and $`S` is a nonempty set of relations on the union of $`C` and $`E`.
>
> — Bunge, *Treatise on Basic Philosophy* Vol. 4, 1979, Ch. 1

The three components:

- $`C(\sigma)` — **Composition**: not the collection of all parts, but the set of *atoms* — those parts that independently enter into the system's relations. For a social system, the atoms are whole individuals, not their brains.
- $`E(\sigma)` — **Environment**: the set of all things, not components of $`\sigma`, that act on or are acted upon by its components. Bunge is precise: this is the *immediate* environment, not the rest of the universe. "The immediate environment of a thing is the composition of its next supersystem."
- $`S(\sigma)` — **Structure**: the set of relations among components and between components and environment, including both bonding relations (causal connections) and nonbonding relations (spatial configuration, for example).

Bunge adds one primitive that Klir lacks: *environment*. A system exists *within* something, and that something is a first-class component of its description. Where Klir asks "what are the parts and how are they related?", Bunge asks "what is inside, what is outside, and how do they interact?"

Three coherence constraints bind the triple together, enforced at the type level:

1. $`C \cap E = \emptyset` — components and environment do not overlap. If the thermometer appeared in both $`C` and $`E`, the formalism would claim the same entity is simultaneously inside and outside the system. The compiler rejects this.
2. All relations in $`S` are defined on $`C \cup E` — no dangling references. A bond (satellite, controller) where satellite appears in neither $`C` nor $`E` would reference an entity the system does not know about.
3. At least two distinct components must be bonded: there exist $`a, b \in C` with $`a \neq b` and $`a` bonded to $`b`. Otherwise the collection is a heap, not a system. $`C` = \{thermometer\} with no bonds has thinghood but not systemhood.

```lean
#check @ConcreteSystem
```

**Formalization choice.** Bunge writes "set of relations," plural. The formalization collapses this to a single flat relation `Set (α × α)`. Chapter 3 verifies this is a faithful quotient: flattening commutes with the internal/external decomposition, so no theorem depends on the distinction.

The `ActsOn` typeclass provides Bunge's action relation — `a ▷ b` means "a modifies b's trajectory." This is the primitive notion of bonding: causal influence between concrete things.

**A 47-year-old error.** Bunge's Definition 1.6 (*Treatise on Basic Philosophy*, Vol. 4, Ch. 1, 1979) states that the subsystem relation is *"reflexive, asymmetric, and transitive."* No relation can be both reflexive and asymmetric. Reflexivity gives $`x \leq x` for all $`x`; asymmetry requires $`x \leq y \implies \neg(y \leq x)` — substituting $`y = x` yields a contradiction. The compiler rejected the asymmetry claim. The correct property is **antisymmetry**: $`\sigma_1 \leq \sigma_2` and $`\sigma_2 \leq \sigma_1` implies equality of their CES triples as ordered tuples (composition, environment, and structure are pairwise equal as sets). This error has been in print since 1979.

**Note on CESM.** Later work (Bunge, *Systemism*, 2000) extends the triple to $`\langle C, E, S, M \rangle` adding mechanism. The 1979 *Treatise* uses the triple. The formalization encodes the 1979 definition; mechanism enters through Mobus's transforms $`\tau`.

**The thermostat as a Bunge system.**

$$`C = \{\text{thermometer}, \text{controller}, \text{furnace}\}`

$$`E = \{\text{room}, \text{outsideAir}\}`

$$`S = \{(\text{room} \triangleright \text{thermometer}),\; (\text{thermometer} \triangleright \text{controller}),\; (\text{controller} \triangleright \text{furnace}),\; (\text{furnace} \triangleright \text{room})\}`

A modeling decision: the room is environment because the thermostat acts *on* the room — the room is what the system is trying to regulate. A subtlety: outsideAir appears in $`E` but no component acts on it or is acted upon by it directly — it contributes a thermal disturbance, not a bond. Strictly, outsideAir is closer to Mobus's milieu $`M` (ambient conditions) than to Bunge's environment (bonded external things). We include it in $`E` here for continuity with the Mobus example; the tension is real and illustrates how the boundary between Bunge's and Mobus's ontologies is not always clean.

**Emergence, briefly.** Philosophical debates about emergence can span hundreds of pages. Let $`\mathcal{P}(\sigma, t_1)` be the properties of a system before assembly and $`\mathcal{P}(\sigma, t_2)` the properties after. The formal definition reduces to set operations:

$$`P_{emergent} = \mathcal{P}(\sigma, t_2) \setminus \mathcal{P}(\sigma, t_1)`

$$`P_{lost} = \mathcal{P}(\sigma, t_1) \setminus \mathcal{P}(\sigma, t_2)`

$$`P_{novel} = P_{emergent} \cup P_{lost} = \mathcal{P}(\sigma, t_1) \mathbin{\triangle} \mathcal{P}(\sigma, t_2)`

Qualitative novelty is the symmetric difference. `simp` closes it. Bunge's Definition 1.13 on emergence, once formalized, is a one-liner. This captures the *bookkeeping* of emergence — which properties appear and disappear — not its metaphysics. The philosophical claim that emergent properties are irreducible to lower-level descriptions is a separate assertion that no set operation can settle.

# Mobus: The 8-Tuple

$$`S_{i,l} = \langle C, N, E, G, B, T, H, \Delta t \rangle_{i,l}`

> The development of this approach was inspired originally by Klir (2001) although he, by his own claim, was a radical constructivist, whereas this work is inclined toward a realist interpretation. ... We start with a principle-based definition and then apply mathematics as a way to provide a structure for "holding" the details of a system description. We will not be doing math as much as using math.
>
> — Mobus, *Systems Science*, Ch. 4, 2022

Mobus elaborates Klir in a different direction from Bunge, toward engineering methodology. Where Bunge asks "what *is* a system?", Mobus asks "how do you *describe* one?" He shares Klir's starting point but rejects his constructivism, and where Bunge and Klir treat the definition as an end in itself, Mobus treats it as a scaffold for capturing real-world system descriptions.

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

1. Internal network nodes $`=` components — the flow graph cannot reference entities that are not part of the system. No ghost nodes.
2. $`C \cap O = \emptyset` — the same disjointness as Bunge. An entity is either a component or an environmental object, never both.
3. $`I \subseteq C` — interface components must actually be components. The boundary cannot claim an entity the system does not contain.
4. External flows are *bipartite* between $`O` and $`I` — no flow connects two components (those are internal) or two environmental objects (those are co-environmental). Every cross-boundary flow has one foot inside and one foot outside.
5. External flow nodes $`\subseteq O \cup I` — no orphan endpoints. Every participant in an external flow is either an environmental object or an interface component.

The bipartite constraint alone *implies* boundary completeness: all interaction between system and environment passes through the boundary. This is derived, not axiomatized. In the thermostat: every flow between system and room must pass through thermometer or furnace. No backdoor.

**Formalization choice.** The first five fields ($`C, N, E, G, B`) are structurally active — they participate in proofs. The last three ($`T, H, \Delta t`) are parametric — carried data with no structural role in the ontology. This is a deliberate scope decision, not an oversight: transforms are domain-specific, history is implementation-specific, and time scale is observational. The formalization captures *what a system has*, not *what it does*. Mobus himself might object — in his engineering reading, the transforms *are* the system. What we formalize is the structural skeleton that all traditions share; the dynamics that distinguish them remain outside the current scope.

**The thermostat as a Mobus system.**

$$`C = \{\text{thermometer}, \text{controller}, \text{furnace}\}`

$$`N: \text{thermometer} \xrightarrow{\text{mV}} \text{controller} \xrightarrow{\text{on/off}} \text{furnace} \xrightarrow{\text{BTU}} \text{thermometer}`

$$`E = \langle O, M \rangle \quad \text{where } O = \{\text{room}\},\; M = \text{outsideAir (ambient thermal)}`

$$`B = \langle P, I \rangle \quad \text{where } I = \{\text{thermometer}, \text{furnace}\}`

$$`T = \text{Unit}, \quad H = \text{Unit}, \quad \Delta t = \text{Unit}`

The last three fields are blank — Unit. No formal theory of what the controller *does*, no history, no time scale. That absence is the gap this document is building toward.

```lean
#check thermostatMobus
```

---

The three definitions above are *structural*. Their characteristic move is inward: relations are defined over things, structure over composition, networks over components. The arrows in their shape categories converge toward the system's core.

The next three traditions reverse this orientation. They begin not with what a system _is_ but with what it _does_, and their arrows radiate outward from state. Where Mobus enumerates eight fields of internal structure, Mesarovic refuses to open the box at all.

# Mesarovic: S ⊆ V × Y

$$`S \subseteq V \times Y`

> We define a system $`S` as a relation on abstract sets: $`S \subseteq \prod_{i \in I} V_i`. ... This definition is deliberately kept at the most general level to cover, in a unified manner, the widest possible class of systems of interest.
>
> — Mesarovic & Takahara, *General Systems Theory*, 1975, Def. 1.1

Mesarovic begins where the others do not: with pure observation. A system is not components or boundaries — it is a relation between what goes in and what comes out. Two sets and a subset:

- $`V` — **Input**: the set of possible inputs (stimuli, perturbations, driving signals)
- $`Y` — **Output**: the set of observable responses
- $`S \subseteq V \times Y` — **System**: the relation itself. Not a function — the same input may yield different outputs

This is the most parsimonious definition in the tradition. No state, no time, no structure. A system *is* its input-output behavior. Mesarovic refuses to answer "how?", only "what does it do?"

```lean
#check MesarovicIOShape
```

The shape category is *discrete*: two objects, zero generating arrows. No dependency is asserted between input and output. The system is the relation $`S`, not a mapping from one to the other. This is the formal content of Mesarovic's extensional stance — the system is identified with its behavior, full stop.

Mesarovic then asks: when _can_ a system be captured by a state? This is not an idle question. Most real systems — economies, ecologies, organizations — resist state-space representation because their future behavior depends on their entire history, not a compressible summary. Admitting a global state is a commitment that most interesting systems fail. Definition 1.4 introduces the canonical extension for those that pass: if a global state $`x \in X` exists such that the response at any time depends only on $`x` and the input, the system admits a state-space representation:

$$`F: X \times \Omega \rightarrow Y`

where $`\Omega` is the space of admissible input functions. The three-object shape emerges:

```lean
#check MesarovicShape
```

Two arrows radiate from `globalState` — one toward input (the state constrains which inputs are admissible), one toward output (the state determines the response). This is the first *outward* shape we encounter: state is the source, not the target.

*The thermostat as a Mesarovic system.*

$$`V = \{\text{setpoint adjustments}, \text{ambient temperature changes}\}`

$$`Y = \{\text{room temperature trajectories}\}`

$$`S = \text{the set of (input, output) pairs the thermostat can produce}`

Mesarovic's thermostat is a black box. We observe what goes in and what comes out. The thermometer, controller, and furnace are invisible — they may or may not exist. This is the sharpest possible contrast with Mobus, who begins by enumerating exactly those components.

# Wymore: Z = (S, I, O, N, R)

$$`Z = (S_Z, I_Z, O_Z, N_Z, R_Z)`

> A system is determined by its state space, its input space, its output space, a next-state function, and a readout function. ... The fundamental concept is that of a system design, i.e., a mathematical model which can be used to predict the future behavior of a system.
>
> — Wymore, *Model-Based Systems Engineering*, 1993, Ch. 3

Where Mesarovic asks "what does it do?", Wymore asks "given its current state and an input, what happens next?" This is the engineer's definition. Five components:

- $`S_Z` — **State space**: the set of all possible internal configurations
- $`I_Z` — **Input space**: what the environment can send
- $`O_Z` — **Output space**: what can be observed
- $`N_Z: S \times I \rightarrow S` — **Next-state function**: dynamics. Given state and input, the successor state
- $`R_Z: S \rightarrow O` — **Readout function**: observation. Given state, what the system reveals

Wymore adds what Mesarovic deliberately omits: commitment to state, to dynamics, and to time. The admissible input function space $`\Omega` reappears as a first-class component — not all input sequences are physically realizable, and the system definition must say which ones are.

```lean
#check WymoreShape
```

Four objects, three arrows — all radiating from `state`. The shape adds a fourth vertex that no other tradition has: `time`. The arrow `stateOnTime` asserts that state is parameterized by a temporal index. This is structurally significant: when we compare Wymore's shape to Mobus's, the time vertex requires a *length-2 path* through boundary to find its image.

```lean
#check wymore_stateOnTime_length
```

Mobus does not have a direct "state at time $`t`" — temporal reasoning must be mediated through the interface structure. The path length is the formal measure of this disagreement. Wymore's willingness to commit to time is what makes his framework useful for simulation and what makes it fragile for systems whose temporal structure is not known in advance.

*The thermostat as a Wymore system.*

$$`S_Z = \mathbb{R} \quad \text{(room temperature)}`

$$`I_Z = \mathbb{R} \times \{0, 1\} \quad \text{(setpoint, furnace command)}`

$$`O_Z = \mathbb{R} \quad \text{(displayed temperature)}`

$$`N_Z(s, i) = s + \alpha(i_{\text{furnace}} \cdot Q - \beta(s - T_{\text{outside}})) \quad \text{(thermal dynamics)}`

$$`R_Z(s) = s \quad \text{(thermometer reads room temperature)}`

Wymore's thermostat computes. Given the current room temperature and the furnace command, it produces the next temperature. The readout is identity — the thermometer reports what it measures. Compare to Mesarovic's black box: same thermostat, but now we have committed to how it works, not just what it does.

# Myers: S = ⟨State, Out, In, expose, update⟩

$$`S = \langle \text{State}, \text{Out}, \text{In}, \text{expose}, \text{update} \rangle`

> A deterministic system is a lens $`(\text{expose}, \text{update}) : (\text{State}, \text{State}) \leftrightarrows (\text{In}, \text{Out})`. The key property of lenses is that they compose.
>
> — Myers, *Categorical Systems Theory*, 2023, §2.1

Myers arrives at a definition structurally identical to Wymore's at a single time step — state, input, output, two functions — but wraps it in the categorical machinery of *lenses*. The payoff is compositionality: two systems whose output-input types match can be composed, and the result is again a system. No other tradition proves this as a general theorem.

- **State** — internal configuration
- **Out** — observable output
- **In** — accepted input
- **expose**: State → Out — the observation function (Wymore's readout)
- **update**: State × In → State — the dynamics function (Wymore's next-state)

```lean
#check MyersShape
```

Three objects, two arrows from `state`. Drop the `time` vertex from Wymore and you have Myers. The structural equivalence is exact at one time step — the difference is that Myers embeds this in a composition framework where Wymore treats it as a standalone machine.

The comparison functor from Mobus to Myers reveals the statics-dynamics divide:

```lean
#check myers_update_unreachable
```

No position in Mobus's 8-tuple maps to Myers's `update`. Every Mobus structural constraint — network on components, boundary in components, external flows on environment — maps to `expose`, the observation interface. But `update`, the dynamics function, has no preimage. Mobus captures what systems *are*. Myers captures how they *behave*. The statics-dynamics divide is not a matter of emphasis — it is a categorical gap, visible in the fiber structure of the comparison functor.

```lean
#check myers_fiber_input
```

The input fiber is also empty: no Mobus position maps to Myers's input. Mobus has no formal concept of "what the environment sends." The 8-tuple's environment field ($`E = \langle O, M \rangle`) describes what is *outside*; Myers's input describes what comes *in*. Presence is not entry.

*The thermostat as a Myers system.* The dynamics are Wymore's. What Myers adds is the ability to compose. Define two lenses:

$$`\text{Plant} = (\text{expose}_P, \text{update}_P) : \text{RoomState} \leftrightarrows (\text{TempReading}, \text{HeatInput})`

$$`\text{Controller} = (\text{expose}_C, \text{update}_C) : \text{SetpointState} \leftrightarrows (\text{HeatCommand}, \text{TempReading})`

The plant lens observes room temperature and accepts heat. The controller lens reads temperature and commands the furnace. Because their output-input types match ($`\text{TempReading}` flows from plant to controller, $`\text{HeatCommand}` flows back), Myers composes them:

$$`\text{Thermostat} = \text{Controller} \circ \text{Plant}`

The result is again a lens — a closed-loop system with its own state, expose, and update. Wymore can describe either component; Myers can describe their composition as a system in the same formalism. This is the structural payoff of the lens framework, and it is exercised nowhere in the six other traditions.

# Joslyn: Constraint, Control, and Semantics

$$`S \subseteq X = \prod_{i=1}^{n} X_i`

> A system is a constraint: a restriction of the possible to the actual. ... The important question is not "what states does a system occupy?" but "what states does it exclude, and how?"
>
> — Joslyn, "Semantic Control Systems," 1995/2000; building on Ashby, 1956

Joslyn asks a different question from every tradition above: _what does the system prevent, and how does it know?_

The intellectual lineage is specific. Ashby (1956) defined constraint as a subset of a product space and variety as the logarithm of distinguishable states. Pattee (1970s-1990s) formalized the "epistemic cut" between rate-dependent physical dynamics and rate-independent symbolic constraints. Rosen (1991) formalized cyclic closure to efficient causation in living systems using category theory — his (M,R)-systems share the cyclic shape property, but define a subclass (living systems) rather than systems in general. Joslyn (1995) cites all three, but produces something none of them did: a single framework that combines Ashby's constraint quantification, Pattee's semiotic distinction, and cyclic structure into a general set-theoretic definition of system with typed functional relations.

Where Mesarovic defines a system by which states it _occupies_, Joslyn defines it by which states it _excludes_. The complement $`C := X - S` is the constraint — the set of states the system rules out. Four conceptual layers build upward:

*Definition 5* (base). A system is a subset $`S \subseteq X = \prod X_i` — the same starting point as Mesarovic. What states does the system occupy?

*Definition 6* (the flip). The constraint $`C := X - S`. Now the question reverses: what states are ruled out? A system with more constraint has fewer possible states and more "systemness." A heap rules out nothing.

*Definition 21* (variety). Joslyn quantifies systemness along two axes:
- _Dimensional variety_: how many variables $`X_i` are constrained (how many dimensions does the system span?)
- _Cardinal variety_: how much of each $`X_i` is excluded (how tightly does the system constrain each variable?)

No other tradition offers a quantitative measure of how constrained a system is. Two systems can now be compared not just by their structure but by the degree to which they restrict possibility.

*Proposition 29* (control₂). A system that _maintains_ its own constraints against disturbance must have a feedback loop. This is not assumed — it is derived. External disturbance pushes the system toward states in $`C` (the excluded region). Maintaining $`S` requires an effector that counteracts the disturbance, an afferent path carrying information about the current state back to the controller, and an efferent path through which the controller acts on the controlled variables. This afferent-efferent loop is the minimal structure of a control₂ system.

The controller, effector, and controlled variables form a cycle. Joslyn then makes a move no other tradition attempts: he types the functional relations inhabiting the loop. A law is discovered (gravity constrains orbits). A rule is selected (the thermostat setpoint is chosen by an occupant). A code is constructed (DNA encodes proteins). The semiotic type — law, rule, code — determines how the constraint can change, who or what can change it, and whether the system can modify its own constraints. This is a structural claim about the _kind_ of relation, not just its existence.

```lean
#check JoslynShape
```

Two properties distinguish this shape category from all six others. First, it is the only _cyclic_ shape. Every other tradition's shape category is a DAG — a directed acyclic graph where morphisms compose along finite paths that terminate. Joslyn's has a cycle: effector → controlled (efferent) and controlled → effector (afferent). In the free category on this quiver, the cycle generates infinitely many morphisms — alternating paths of arbitrary length. The shape category is infinite where all others are finite.

Second, Joslyn's is the only tradition that formally distinguishes the _kind_ of relation inhabiting its functional positions. The other six traditions encode _that_ components are related and _how_ (structurally). Joslyn encodes _what kind_ of relation it is — physical law, chosen rule, or constructed code — and this typing has consequences for what the system can do to itself.

These two properties — feedback closure and semiotic typing — are precisely what the common core embedding cannot preserve:

```lean
#check @klirToJoslyn
```

Klir's walking arrow maps _things_ to `controlled` and _relation_ to `effector`, with the arrow landing on `efferent` — the outward leg. The afferent return path and the disturbance arrow have no counterpart in the walking arrow. This is why $`K \cong \mathbf{2}` is maximal: the walking arrow cannot capture cycles. What Joslyn adds to the tradition — feedback, closure, semantic content — is what the common core necessarily loses.

*The thermostat as a Joslyn system.*

$$`X = X_{\text{roomTemp}} \times X_{\text{outsideAir}}`

$$`S = \{(t, a) \in X \mid t_{\text{min}} \leq t \leq t_{\text{max}}\}`

$$`C = X - S = \{(t, a) \mid t < t_{\text{min}} \text{ or } t > t_{\text{max}}\}`

$$`O_E = \text{controller (compares setpoint to measured temp)}`

$$`O_I = \{\text{furnace (effector)}, \text{thermometer (sensor)}\}`

The thermostat is a control₂ system because it maintains $`S` against thermal disturbance. The afferent path: thermometer reads room temperature. The efferent path: controller commands furnace. The constraint $`C` is the set of temperatures the thermostat is designed to prevent. And the setpoint is a _rule_, not a law. It is chosen, not discovered. Someone set it to 68°F. They could have set it to 72°F. The constraint is semantic, not physical, and this distinction has no formal expression in any of the six traditions above.
