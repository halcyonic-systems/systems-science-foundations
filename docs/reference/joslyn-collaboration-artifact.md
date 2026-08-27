# A Formal Systems Ontology and Its Open Frontier

**Shingai Thornton**
*Halcyonic Systems*

*Draft for Cliff Joslyn — Technical proposal, not a finished paper.*

---

## 0. Prefatory Note

I noticed something in the summer 2025 paper that I couldn't let go of: Mobus's 8-tuple and Bunge's CES triple are eerily similar — same decomposition into components, environment, and structure — yet Mobus never cites Bunge. I wrote it up as a "systematic extension." Then you asked the right question: *does Mobus actually cite Bunge?* I checked. He doesn't. Neither references the other.

That killed the "extension" framing and opened the real question: *how are two independently developed frameworks this compatible?* The answer turned out to be Klir. Both cite him. Both inherit T = `Set α` and R = `Set (α × α)` from his (T, R) definition without changing the mathematical type. The formalization proves this — the commuting triangle is `rfl`.

You gave me thirty red-text comments on that paper. Thirteen mapped directly to machine-checked code. Your question about the type of S — *"S is a set of sets of tuples, right?"* — forced a design decision the Lean compiler settled in 146 lines and two theorems.

This document presents what that process produced, and where it reaches its limits — limits that your variety-theoretic and semiotic framework is precisely designed to resolve.

---

## 1. The Mathematical Landscape

The general systems tradition contains several set-theoretic definitions of "system" that are not competing alternatives but *layers* of increasing ontological commitment. This section presents three — Klir, Bunge, and Mobus — in their formal definitions, with proper citations and the Lean 4 encodings.

### 1.1 Klir: S = (T, R)

Klir defines a system as two things: a set of entities and a relation among them (Klir, *Facets of Systems Science*, 2001, Eq. 1.1).

> A system S is an ordered pair S = (T, R), where T is a set of things (thinghood) and R is a relation on T (systemhood).

A thing becomes a system when you specify which of its parts are related. This is the simplest formal definition of system in the general systems tradition — and, as we will prove, the common ancestor of both Bunge and Mobus.

```lean
structure KlirSystem (α : Type*) where
  things : Set α
  relation : Set (α × α)
```

The type is transparent: `things` is a set over an arbitrary carrier type `α`, and `relation` is a set of ordered pairs. No time, no state, no environment, no boundary. Just T and R.

### 1.2 Bunge: ⟨C, E, S⟩

Bunge adds one primitive that Klir lacks: *environment*. A system exists within something, and that something is a first-class component of its description (Bunge, *Treatise on Basic Philosophy Vol. 4: Ontology II*, 1979, Def. 1.1–1.2).

> The ordered triple ⟨σ = C, E, S⟩ is (or represents) a system over T iff C and E are mutually disjoint subsets of T, and S is a nonempty set of relations on the union of C and E.

Where:
- **C** (composition): the set of components
- **E** (environment): the set of external things bonded with components
- **S** (structure): the set of relations among C and between C and E

```lean
structure ConcreteSystem (α : Type*) [ActsOn α] where
  composition : Set α
  environment : Set α
  structure' : Set (α × α)
  disjoint : composition ∩ environment = ∅
  structure_on : ∀ p ∈ structure',
    p.1 ∈ composition ∪ environment ∧
    p.2 ∈ composition ∪ environment
  bondage_nonempty : ∃ a ∈ composition, ∃ b ∈ composition,
    a ≠ b ∧ Bonded a b
```

Three coherence constraints are enforced at the type level: C ∩ E = ∅, all relations are defined on C ∪ E, and at least two distinct components are bonded. The `ActsOn` typeclass provides Bunge's action relation `a ▷ b` ("a modifies b's trajectory") as the primitive notion of bonding.

**Note on CESM.** Later work (Bunge, "Systemism," *Journal of Socio-Economics*, 2000) extends this triple to a 4-tuple ⟨C, E, S, M⟩ adding *mechanism* as a fourth component. The 1979 *Treatise* uses the triple only. The formalization encodes the 1979 definition; mechanism enters through Mobus's transforms τ.

### 1.3 Mobus: The 8-Tuple

Mobus elaborates Klir's (T, R) in a different direction from Bunge — toward engineering methodology. Where Bunge asks "what *is* a system?", Mobus asks "how do you *describe* one?" (Mobus & Kalton, *Principles of Systems Science*, 2015, Ch. 4; Mobus, *Systems Science*, 2022, book-revisions Eq. 1). He cites Klir (2001) explicitly: *"The development of this approach was inspired originally by Klir (2001)"* (Ch. 4, p. 14).

The formal definition is an 8-tuple:

```
S_{i,l} = ⟨C, N, E, G, B, T, H, Δt⟩_{i,l}
```

| Field | Symbol | Content |
|---|---|---|
| Components | C | Set of entities at level l |
| Internal network | N = ⟨C, L⟩ | Directed flow graph among components, with capacity labels |
| Environment | E = ⟨O, M⟩ | Discrete objects O + opaque milieu M |
| External flows | G | Bipartite flow graph between O and interface components |
| Boundary | B = ⟨P, I⟩ | Boundary properties P + interface components I ⊆ C |
| Transforms | T | Domain-specific processing functions |
| History | H | Stored knowledge / memory |
| Time scale | Δt | Temporal resolution |

```lean
structure MobusSystem (α κ μ π τ η δ : Type*) where
  components : Set α
  internalNetwork : FlowNetwork α κ
  environment : MobusEnvironment α μ
  externalFlows : FlowNetwork α κ
  boundary : MobusBoundary α π
  transforms : τ
  history : η
  timeScale : δ
  -- Five coherence constraints:
  network_components : internalNetwork.nodes = components
  disjoint : components ∩ environment.objects = ∅
  interfaces_sub : boundary.interfaces ⊆ components
  bipartite : IsBipartiteFlow externalFlows
                environment.objects boundary.interfaces
  externalFlows_nodes : externalFlows.nodes ⊆
                          environment.objects ∪ boundary.interfaces
```

Seven type parameters. Five coherence constraints enforced by the compiler. The first five fields (C, N, E, G, B) are structurally active — they participate in proofs. The last three (T, H, Δt) are parametric — carried data with no structural role in the ontology.

### 1.4 The Mesarovic Connection

Your own formal base — System₁ as S ⊆ X₁ × ⋯ × Xₙ with constraint C := X − S (Joslyn, "Semantic Control Systems," *World Futures* 45, 1995, Def. 5) — sits in the same tradition. Klir's (T, R) is the relational core of Mesarovic's abstract systems theory, specialized to binary relations. The commuting triangle below operates on Klir's variant, but the structural mappings extend naturally to the full Mesarovic product.

---

## 2. The Commuting Triangle

Bunge (1979) read Klir — he cites Klir and Valach (1967) and Klir and Rogers (1977) in his bibliography. Mobus (2022) read Klir — he cites Klir (2001) explicitly as inspiration. **Neither Bunge nor Mobus references the other.** They developed independently from a shared Klir root, 43 years apart, using different notation, terminology, and motivating examples.

The formalization discovers that both paths from Mobus's 8-tuple back to Klir's (T, R) — via Bunge or directly — produce the same result. Not merely the same up to isomorphism, but *definitionally identical*:

```
          toBunge
    Mobus -------→ Bunge
      \              |
       \  toKlir    | toKlir
        \           |
         ↘          ↓
           Klir
```

### 2.1 The Projection Maps

**Bunge → Klir** (forget environment):

```lean
def ConcreteSystem.toKlir (s : ConcreteSystem α) :
    KlirSystem α where
  things := s.composition
  relation := s.structure'
```

**Mobus → Bunge** (forget milieu, capacity, boundary, transforms, history, time scale):

```lean
def MobusSystem.toBunge (sys : MobusSystem α κ μ π τ η δ)
    (hflow : FlowInducesAction sys.internalNetwork)
    (hedge : sys.internalNetwork.edges.Nonempty) :
    ConcreteSystem α where
  composition := sys.components
  environment := sys.environment.objects    -- milieu M lost
  structure' := sys.totalRelation           -- capacity κ lost
  disjoint := sys.disjoint
  structure_on := sys.totalRelation_on
  bondage_nonempty := ⟨...⟩                 -- from hedge + hflow
```

**Mobus → Klir** (forget everything except T and R):

```lean
def MobusSystem.toKlir (sys : MobusSystem α κ μ π τ η δ) :
    KlirSystem α where
  things := sys.components
  relation := sys.totalRelation
```

### 2.2 The Theorem

```lean
theorem triangle_commutes
    (sys : MobusSystem α κ μ π τ η δ)
    (hflow : FlowInducesAction sys.internalNetwork)
    (hedge : sys.internalNetwork.edges.Nonempty) :
    (sys.toBunge hflow hedge).toKlir = sys.toKlir := rfl
```

**The proof is `rfl`** — reflexivity. The Lean type-checker confirms that the two paths produce not just equal but *definitionally identical* `KlirSystem` values. This traces to both Bunge and Mobus inheriting T = `Set α` and R = `Set (α × α)` from Klir without changing the mathematical type.

This was not claimed by any author. It was *discovered* through formalization.

### 2.3 Information Loss

The bridge is a projection: many Mobus 8-tuples map to the same Bunge triple. Six categories of information have no Bunge counterpart:

| Loss Category | Mobus field | Bunge counterpart | What is lost |
|---|---|---|---|
| Milieu | M in E = ⟨O, M⟩ | E is a set of things only | Ambient conditions (temperature, pressure) |
| Capacity | κ on flow edges | S is pairs, not weighted | How much flows (BTUs, bits, dollars) |
| Boundary properties | π in B = ⟨P, I⟩ | No boundary concept | Permeability, insulation |
| Transforms | τ | No functional component | What things *do* to their inputs |
| History | η | No memory component | Accumulated knowledge |
| Time scale | δ | Time-indexed but unformalized | Temporal resolution |

The formal statement: two Mobus systems differing only in these six categories project to the same Bunge CES triple.

```lean
theorem toBunge_eq_of_structural_eq
    (sys₁ sys₂ : MobusSystem α κ μ π τ η δ)
    (hc : sys₁.components = sys₂.components)
    (he : sys₁.environment.objects = sys₂.environment.objects)
    (hs : sys₁.totalRelation = sys₂.totalRelation) :
    -- Then the three CES fields are equal:
    (sys₁.toBunge hflow₁ hedge₁).composition =
      (sys₂.toBunge hflow₂ hedge₂).composition ∧
    (sys₁.toBunge hflow₁ hedge₁).environment =
      (sys₂.toBunge hflow₂ hedge₂).environment ∧
    (sys₁.toBunge hflow₁ hedge₁).structure' =
      (sys₂.toBunge hflow₂ hedge₂).structure' :=
  ⟨hc, he, hs⟩
```

This is **independent convergence with formally characterized divergence**. The `rfl` proofs on the preserved fields are not trivially expected — they are empirical findings that two researchers, using different notation and motivating examples, decomposed a system in structurally compatible ways.

---

## 3. What the Compiler Found

The Lean type-checker is not just a verification tool — it is an instrument of discovery. In 864 lines of Bunge formalization, it forced four interpretive decisions that 47 years of scholarly reading had not resolved.

### 3.1 A 47-Year-Old Error

Bunge's Definition 1.6 states that the subsystem relation is *"reflexive, asymmetric, and transitive."*

No relation can be both reflexive and asymmetric. Reflexivity gives x ≤ x for all x; asymmetry requires that x ≤ y implies ¬(y ≤ x) — but substituting y = x yields ¬(x ≤ x), contradicting reflexivity.

The compiler rejected the asymmetry claim. The correct property is **antisymmetry**: if σ₁ ≤ σ₂ and σ₂ ≤ σ₁, then their CES triples are equal.

```lean
theorem subsystem_antisymm_components
    (h₁₂ : Subsystem σ₁ σ₂) (h₂₁ : Subsystem σ₂ σ₁) :
    σ₁.composition = σ₂.composition ∧
    σ₁.environment = σ₂.environment ∧
    σ₁.structure' = σ₂.structure' :=
  ⟨Set.Subset.antisymm h₁₂.1 h₂₁.1,
   Set.Subset.antisymm h₂₁.2.1 h₁₂.2.1,
   Set.Subset.antisymm h₁₂.2.2 h₂₁.2.2⟩
```

This makes the subsystem relation a **partial order** (reflexive, antisymmetric, transitive) — not a strict order as Bunge's wording implies. The error has persisted through every edition and every commentary.

### 3.2 A Hidden Cross-Volume Dependency

Bunge's Corollary 1.1 asserts: *"The universe is the only system closed at all times."*

The formalization proves this as `Iff.rfl` — definitional identity. A system is closed iff its environment is empty. The corollary says the universe is the only thing with empty environment. But this is vacuously true within Chapter 1 alone: nothing in the chapter constrains which systems have empty environments. The substantive content comes from Postulate 5.10 in Volume 3 (*"every thing except the universe interacts with some other thing"*), which the formalization does not assume.

The compiler made an invisible cross-volume dependency structurally undeniable.

### 3.3 Your Question About S — Answered

You asked (A1): *"'Set of relations' literally means S is a set of sets of tuples, right?"*

Yes. But the formalization proves it doesn't matter for the theorems we need:

```lean
theorem flatten_internal_commutes
    (r : RichConcreteSystem α) :
    ⋃₀ r.internalFamily =
    internalProjection r.composition r.flatten
```

Take the family of relations {Rᵢ}, extract the internal part of each, then union — you get the same result as first flattening to ⋃Rᵢ, then extracting internals. The flat encoding is a faithful quotient. Both readings are consistent, and the flat one loses nothing the proved theorems depend on.

### 3.4 Boundary Completeness — Derived, Not Axiomatized

Boundary completeness — the systems-theoretic property that all system-environment interaction is mediated by the boundary — is not assumed as an axiom. It follows structurally from the bipartite constraint on Mobus's external flow graph G:

```lean
theorem MobusSystem.boundaryComplete
    (sys : MobusSystem α κ μ π τ η δ) :
    BoundaryComplete sys.boundary sys.externalFlows
      sys.environment.objects :=
  bipartite_implies_boundary_complete sys.boundary
    sys.externalFlows sys.environment.objects sys.bipartite
```

The right constraint at definition time makes the property a *derived consequence*. This is not an isolated trick — it exemplifies what formalization reveals: which properties are independent axioms and which are structural corollaries.

---

## 4. The Thermostat: Three Descriptions of One System

The thermostat is the canonical example of a control₂ system — you used it in the 1995 paper to derive the internal-state requirement (Proposition 29) and the semantic-relation argument. Here we formalize the same system under all three frameworks to show what each captures and what each misses.

The physical setup: a room with a thermostat (thermometer + controller), a furnace, and outside air as a disturbance source. The controller reads the temperature, compares it to a setpoint, and commands the furnace on or off.

The full Lean file is `Systems/Examples/Thermostat.lean` — 160 lines, zero `sorry`s, fully compiled. What follows is a guided reading.

### 4.1 Entities and Action

Five entities. Four causal bonds:

```lean
inductive Entity where
  | thermometer | controller | furnace | room | outsideAir
  deriving DecidableEq

instance : ActsOn Entity where
  actsOn
    | room, thermometer => True       -- room temp modifies thermometer state
    | thermometer, controller => True  -- measurement signal
    | controller, furnace => True      -- on/off command
    | furnace, room => True            -- heat delivery
    | _, _ => False
```

A modeling decision lives here: **outsideAir does not act on anything discretely.** Its thermal effect enters through the milieu M (ambient temperature), not a point-source flow. The system does not model the outsideAir → room heat-transfer pathway — it only sees the room temperature via the thermometer. This is the systemic stance in action: the thermostat system's boundary determines what is modeled and what is not.

### 4.2 The Mobus 8-Tuple

We build the Mobus system first, then derive the others by projection. This is both cleaner and more honest — it matches how a systems engineer actually works (detailed model first, then abstractions).

**Components and environment:**

```lean
def comps : Set Entity := {thermometer, controller, furnace}
def envObjs : Set Entity := {room, outsideAir}
def intfs : Set Entity := {thermometer, furnace}
```

Interfaces I = {thermometer, furnace} — both sense from and act on the environment. The controller is purely internal; it does not cross the boundary.

**Internal flow network** (among components):

```lean
def intEdges : Set (FlowEdge Entity Unit) :=
  fun e => (e.source = thermometer ∧ e.target = controller ∧ e.capacity = ())
         ∨ (e.source = controller ∧ e.target = furnace ∧ e.capacity = ())
```

Two edges: thermometer → controller (measurement signal) and controller → furnace (on/off command). Capacity κ = `Unit` — the structural proofs do not depend on the capacity type. In a richer model, κ would distinguish temperature signals from binary commands from heat-energy flows; this is one of the six information categories that Bunge's CES loses.

**External flow network** (crossing the boundary):

```lean
def extEdges : Set (FlowEdge Entity Unit) :=
  fun e => (e.source = room ∧ e.target = thermometer ∧ e.capacity = ())
         ∨ (e.source = furnace ∧ e.target = room ∧ e.capacity = ())
```

Two edges: room → thermometer (temperature sensed) and furnace → room (heat delivered). Both cross between environment objects and interface components — the bipartite constraint holds.

**The full 8-tuple:**

```lean
def thermostatMobus : MobusSystem Entity Unit Unit Unit Unit Unit Unit where
  components := comps
  internalNetwork := intNet
  environment := ⟨envObjs, ()⟩       -- ⟨O, M⟩ with Unit milieu
  externalFlows := extNet
  boundary := ⟨(), intfs⟩             -- ⟨P, I⟩ with Unit boundary props
  transforms := ()                     -- the control rule (parametric)
  history := ()                        -- recent readings (parametric)
  timeScale := ()                      -- polling interval (parametric)
  network_components := rfl            -- N.nodes = C by definition
  disjoint := comps_envObjs_disjoint   -- C ∩ O = ∅
  interfaces_sub := ...                -- I ⊆ C
  bipartite := ...                     -- G crosses between O and I
  externalFlows_nodes := ...           -- G.nodes ⊆ O ∪ I
```

Five coherence constraints, all proved. `network_components` is `rfl` — the internal network's node set is literally defined as `comps`. The disjointness proof uses `nomatch` on impossible constructor equalities. The bipartite proof case-splits on which edge and verifies each crosses the boundary.

The parametric fields (τ, η, δ) use `Unit` — they carry no structural content at this level. The document's §5 describes what meaningful types would be: τ as the if/then control rule, η as recent temperature readings, δ as a 30-second polling interval. These are exactly the information categories that the Mobus→Bunge projection discards.

### 4.3 Bunge and Klir — By Projection

Rather than defining the Bunge and Klir systems independently, we *extract* them from the Mobus 8-tuple via the formal projection maps. This ensures definitional equality and demonstrates the workflow:

```lean
def thermostatBunge : ConcreteSystem Entity :=
  thermostatMobus.toBunge
    thermostat_flow_induces_action
    thermostat_internal_nonempty

def thermostatKlir : KlirSystem Entity :=
  thermostatMobus.toKlir
```

**What `thermostatBunge` contains** (after projection):
- composition = {thermometer, controller, furnace} — exact from Mobus
- environment = {room, outsideAir} — from Mobus `environment.objects` (milieu discarded)
- structure = intNet.toRelation ∪ extNet.toRelation — capacity discarded

The `toBunge` projection requires two witnesses: that internal flows induce Bunge's `ActsOn` relation, and that at least one internal edge exists. Both are proved by case-splitting on the edge set.

**What `thermostatKlir` contains** (after projection):
- things = {thermometer, controller, furnace} — components only
- relation = intNet.toRelation ∪ extNet.toRelation — all 4 causal pairs

A structural observation: **room appears in the relation but not in the thing-set.** The pairs (room, thermometer) and (furnace, room) are in R, but room ∉ T. The Klir projection drops the environmental distinction — room becomes a "phantom" entity, present in the system's relational structure but not counted among its things. This is the formal content of losing the environment component E.

### 4.4 The Triangle on the Thermostat

```lean
theorem thermostat_triangle_commutes :
    thermostatBunge.toKlir = thermostatKlir := rfl
```

`rfl`. Both paths from the Mobus thermostat to the Klir system — via Bunge or directly — produce definitionally identical values. The type-checker confirms this without any proof search.

**What was lost at each step:**

**Mobus → Bunge:** Milieu M disappears (ambient temperature and humidity vanish). Capacity labels disappear (the distinction between a temperature signal, a binary command, and a heat-energy flow is collapsed — all become bare pairs). Boundary properties, transforms, history, and time scale disappear. What remains is C, E = O, and S = the edge relations without labels.

**Bunge → Klir:** Environment E disappears. The distinction between "inside" and "outside" is lost. Room and outsideAir lose their special status as environment — room becomes a phantom in R, outsideAir disappears entirely (it has no bonds).

**But all three descriptions miss the same thing.** The controller's logic — *if temperature < setpoint then turn on furnace* — is a **rule**, not a law. It was selected from a variety of possible control functions. It could have been a PID controller, a bang-bang controller, or a machine-learning policy. The *meaning* of "too hot" → "turn off furnace" is not captured by any structural description. The transforms τ field is the natural home for this content — but it is parametric (`Unit`), carrying no internal theory.

This is precisely your point from the 1995 paper: the feedback function f : Oᵢ → Oₑ *must be a rule (contingent entailment), not a natural law*. Rules are arbitrary, conventional, and selected — exactly the properties of Peircean signs. The formalization reaches its limit here.

---

## 5. The Information Loss Chain, Applied

The thermostat makes the six loss categories concrete:

| Loss category | Thermostat content | Why it matters |
|---|---|---|
| **Milieu M** | Ambient temperature, humidity around the house | The disturbance source Joslyn's control₂ requires — lost in Bunge |
| **Capacity κ** | BTUs from furnace, millivolts from thermometer | The *magnitude* of flows — essential for control engineering, invisible to Bunge |
| **Boundary properties π** | R-value of insulation | Determines how much disturbance penetrates — parametric in Mobus, absent in Bunge |
| **Transforms τ** | The if/then control rule | What the controller *does* — the semantic relation, the rule, the sign |
| **History η** | Recent temperature readings stored by controller | Memory — required for any non-trivial control law (PID needs integral term) |
| **Time scale δ** | 30-second polling interval | Temporal resolution — determines whether the system can track fast disturbances |

Two Mobus thermostats differing only in transforms (one with bang-bang control, one with PID) project to the **same** Bunge CES triple. They are structurally identical — same components, same environment, same relations. They differ only in what the controller *does*, which is exactly the semantic content that the formal ontology cannot yet express.

---

## 6. The Open Frontier — Where Your Framework Enters

### 6.1 What the Formalization Cannot Yet Express

**Variety.** The current formalization has no concept of |X|, |S|, or C = X − S as a *measure* of constraint. Your Definitions 13, 17, 18 — dimensional variety (the number of distinct dimensions n), cardinal variety (the cardinality |S| bounded by 1 ≤ |S| ≤ |X|), and constraint as set subtraction — provide the measure-theoretic layer that the structural ontology lacks.

**The rule/law distinction.** The `ActsOn` typeclass is opaque — a Prop-valued binary relation. It does not distinguish between a natural law (necessary entailment: the ball rolls downhill) and a rule (contingent entailment: the controller turns on the furnace). Your distinction between laws and rules (1995, §4.2) is precisely what `ActsOn` collapses. The thermostat's control function is a rule; gravity is a law. The current formalization represents both as `a ▷ b` — opaque action.

**Control₂.** The formalization can represent that the controller acts on the furnace. It cannot express *active maintenance of a dynamic equilibrium against environmental disturbance* — your Definition 28 (control₂ as invariant constraint₁ on O despite variation in C). This requires temporal reasoning and second-order constraint that the snapshot model does not support.

**The metasystem transition.** The emergence of a new level of control requires your hierarchical variety theory to even state formally.

### 6.2 What Your Framework Provides

**Dimensional and cardinal variety give the 8-tuple a measure.** Mobus's component set C has dimensional variety n = |C|. His capacity κ is a cardinal variety measure on edges. Your two-axis framework (dimensional × cardinal) provides the quantitative layer that his structural definition needs.

**The constraint C = X − S connects directly to Bunge's structure.** Your System₁ constraint is the complement of the system relation within the full product space. Formalizing this would give the Bunge/Mobus framework a *measure of how constrained the system is* — how far S is from the unconstrained product X.

**The semantic layer gives Mobus's transforms internal structure.** The transforms τ in Mobus's 8-tuple are the natural home for your contingent entailments. But τ is currently parametric — an opaque type with no internal theory. Your semiotic framework provides the theory to distinguish:
- τ as a law (necessary entailment, discovered, not selected) — gravitational acceleration
- τ as a rule (contingent entailment, selected from a variety of possible functions) — the controller's if/then logic
- τ as a code (arbitrary, conventional, interpretable) — a sensor reading mapped to a command

This is the classification that makes "too hot" → "turn off furnace" a *sign*, not just a function.

**The hypergraph connection.** Your 2018 work — *Seeking a Categorical Systems Theory via the Category of Hypergraphs* (Joslyn & Purvine, NIST Workshop on Applied Category Theory, 2018) — connects to a finding from the formalization. Mobus's two-network decomposition (N internal, G external) is a natural two-element structure family. We proved that three distinct subsystem orderings exist on structure families (family ⊇ refinement ⊇ flat), with forgetful functors between them that are faithful but not full. Hypergraphs generalize binary relations to n-ary — exactly the step from pairs to families that Bunge's "set of sets of tuples" reading enables.

### 6.3 A Concrete Proposal

**What I bring:**
- A working formalization: 2,956 lines of Lean 4, 104 theorems, zero incomplete proofs
- The LLM-assisted formalization methodology (AITP 2026 submission)
- Deep familiarity with Bunge's and Mobus's frameworks from PhD work under Mobus
- The categorification infrastructure (preorder instances, forgetful functors, bridge factorization)

**What you bring:**
- The variety-theoretic framework — the only rigorous account of dimensional and cardinal variety in the systems literature
- The cybernetic / semiotic tradition — the rule/law distinction and the semantic-relation argument that connects control theory to biosemiotics
- The Mesarovic connection — your System₁ is the natural starting point for extending the commuting triangle to the full abstract systems theory
- The hypergraph intuition — the combinatorial approach to categorical systems theory that complements the foundational approach in this formalization

**Proposed phases** (each builds on the last; Phases 1–3 took ~48 hours of LLM-assisted proving):

| Phase | Content |
|---|---|
| **Phase 4** | Formalize Joslyn's variety-theoretic definitions (Defs 13, 17, 18) as Lean 4 structures. Define `DimensionalVariety`, `CardinalVariety`, and `Constraint` as computable functions on `KlirSystem` or a new `MesarovicSystem` type. |
| **Phase 5** | Formalize control₁ / control₂. Define `ControlSystem` as a metasystem CS = ⟨C, O⟩. Define `Control₂` with invariant-under-variation property. Prove Proposition 29 (control₂ ⟹ internal states) in Lean. |
| **Phase 6** | Connect semantic relations to Mobus's transforms. Define `SemanticRelation` as contingent entailment; show it instantiates τ. Prove the semiotic thesis: control₂ ⟹ semantic relations ⟹ signs. |

The formal ontology is not the endpoint — it is the foundation for **System Language (SL)**, a formally specified, computationally executable language for systems science, implemented in BERT. SL already has 40 typed primitives, 8 composition rules (4 Lean-verified), and working models of four blockchain architectures decomposed into the same 4-subsystem cybernetic structure. Your variety-theoretic and semiotic framework would give SL something no systems language has ever had: a formal account of *what kind of functional relation* inhabits a system — rule or law — and what that distinction implies about meaning, control, and autonomy. Machine-checked proofs at every level transition, from Klir's (T, R) through Mobus's 8-tuple through your semantic control, all the way to executable models.

---

## 6.4 Addendum (2026-08-27): what has happened since — and the question only you can answer

*Everything above stands as written in early 2026. This section is the delta, and it ends
with an ask.*

### Your tradition is now encoded — and it broke the comparison machinery

The formalization grew a shape-category program: each tradition's definition encoded as the
free category on its dependency quiver, with machine-checked comparison functors between
them (Klir, Bunge, Mobus, Myers, Wymore, Mesarović, Spivak — and you). `ShapeJoslyn`
encodes the control loop of Definitions 25/28 and Proposition 29: effector and controlled
positions, efferent and afferent arrows — **a cyclic quiver, the landscape's first**.

That cycle turned out to be load-bearing. Every DAG-shaped tradition has finite hom-sets
and is placed by faithful comparison functors. Yours is not — and this is now a theorem,
not a remark:

> `no_faithful_joslyn_to_klir : ¬ ∃ F : JoslynShape ⥤ KlirShape, F.Faithful`

(`Systems/Category/JoslynIncomparability.lean`; axioms `[propext, Classical.choice,
Quot.sound]`, no `sorry`. The general form is proved once for any cyclic shape: the loop's
powers are distinguished by length, so the feedback hom-set is infinite, and faithfulness
would inject it into a finite one.) The comparison apparatus that places the other seven
traditions **provably cannot reach yours**. Feedback is a boundary of the finite-shape
method — converted from folklore to theorem.

### Your definition is now in the catalogue

The atlas this document gestured at is live at **math.systems**: nine definitions,
verbatim, page-located at build time, provenance-graded, with the floor (the one shared
dependency) as a page of its own. Entry 009 is your Definition 28 (Control₂), transcribed
from the World Futures page images (the PDF's own text layer mangles your subscripts and
flattens your angle brackets — the transcription restores them), with five of your case
rulings encoded: thermostat and the decoupled-envelope thermodynamic pair admitted; the
damped spring, the boiling liquid, and the spinning top refused. Its evidence code is
displayed live and honest — model-drafted until a human pass promotes it, per the
catalogue's own discipline.

One provenance finding from the ingest, offered for your correction: the pipeline graded
Definition 25 (control₁) as a *restatement* — you present it as Turchin's 1992 Principia
Cybernetica definition, "offered again here" — so under the catalogue's restatement rule
the control₁ base is Turchin's and Definition 28 is the first control definition that is
yours alone. If that reading is wrong, it is exactly the kind of correction the catalogue
exists to receive.

### The ask

The incomparability theorem carries a caveat, written into its docstring before anyone
asked you:

> *Presentation-relative: both shapes are encodings of primary texts as dependency
> quivers, and a different defensible encoding of Joslyn 1995 — one that does not make
> the control loop a cycle at quiver level — could dissolve the obstruction. Not a
> maximality result.*

**You are the only person who can rule on whether the cycle is faithful to what you
meant.** Three outcomes, each of which we would count a result:

1. **You defend the cycle** — the incomparability theorem becomes author-endorsed, and
   "feedback is where the finite-shape method stops" stands with the strongest provenance
   a formalization can have.
2. **You propose an acyclic encoding** — e.g. one that unrolls the loop across MST levels,
   which your own hierarchy machinery suggests — and the obstruction dissolves for that
   encoding: a new shape enters the landscape, and presentation-relativity is demonstrated
   live rather than asserted.
3. **You rule both encodings defensible** — the first documented case of one primary text
   supporting two shapes with different comparison behavior, which is the sharpest
   possible exhibit for the layer of validation no kernel checks.

This is round two of a loop you started: your thirty red-text comments on the summer 2025
paper produced thirteen machine-checked answers (§3; `joslyn-feedback-mapping.md`). The
compiler settled what it could. This question it cannot settle — it is yours.

Stated once more, in the vocabulary of your own 2026 abstract: the question is where the
*closure* lives. The encoding drew control₂'s semantic closure as a cycle at quiver level —
one drawing decision, from which everything downstream follows. Whether that closure is
genuinely level-flat or unrolls across a metasystem transition is not a question lattice or
topos machinery settles from outside; it is an interpretant only the author can supply. And
the apparatus asking it is, in miniature, the thing your abstract calls for: symbols with
machine-checked grounding (the gates, the theorems, the located verbatims) joined to human
interpretation that is *recorded as such* (the evidence codes say, for every claim, whether
a machine located it, a model drafted it, or a person ruled on it — who interpreted what,
never blurred).

*(Status note for §7's table: it reflects the February 2026 state. The Category program
has since added the eleven-shape landscape, the embedding theorems, the cyclic
obstruction, and the challenge file `Systems/Challenge.lean` — the one file a skeptical
reader needs, kernel-checked against the library.)*

---

## 7. Codebase Summary

| Phase | Module | Lines | Theorems | Content |
|---|---|---|---|---|
| **1** | Thing.lean | 54 | 5 | Parthood, composition |
| | Bond.lean | 79 | 2 | Action (▷), bonding, bondage |
| | System.lean | 172 | 6 | CES triple, subsystem partial order |
| | Level.lean | 137 | 3 | Hierarchy, ancestry, recursive decomposition |
| | Assembly.lean | 134 | 5 | Assembly, emergence, self-organization |
| | Selection.lean | 128 | 7 | Selective action, composition theorem |
| | State.lean | 141 | 5 | State functions, events, aggregate vs. system |
| **2** | FlowNetwork.lean | 177 | 6 | Directed flows with capacity |
| | Environment.lean | 87 | 2 | ⟨O, M⟩ with parametric milieu |
| | Boundary.lean | 111 | 3 | ⟨P, I⟩ with completeness |
| | Interface.lean | 137 | 8 | Bipartite structure, classification |
| | Tuple.lean | 168 | 3 | 8-tuple with coherence constraints |
| | Bridge.lean | 206 | 8 | Mobus→Bunge projection, info loss |
| **3** | KlirSystem.lean | 146 | 6 | Commuting triangle (`rfl`) |
| **Cat** | SubsystemCategory.lean | 84 | 5 | Preorder → thin category |
| | FlattenFunctor.lean | 105 | 7 | Flatten as functor |
| | OrderingTriangle.lean | 263 | 8 | Three orderings, non-fullness |
| | BridgeFunctor.lean | 111 | 3 | Bridge factorization |
| **Exp** | StructureFamily.lean | 475 | 17 | Rich systems, your A1 question |
| **Ex** | Thermostat.lean | 160 | 5 | Joslyn's thermostat, all 3 frameworks |
| | **Total** | **~3,120** | **109** | **Zero `sorry`s** |

Build: Lean 4.28.0 + Mathlib. Fully reproducible. `lake build` completes with zero errors.

---

## 8. References

### Primary Sources (Formalized)

- Bunge, M. (1979). *Treatise on Basic Philosophy, Vol. 4: Ontology II: A World of Systems.* Reidel.
- Bunge, M. (2000). Systemism: the alternative to individualism and holism. *Journal of Socio-Economics* 29, 147–157.
- Klir, G.J. (2001). *Facets of Systems Science,* 2nd ed. Springer. [Originally Plenum, 1991.]
- Mobus, G.E. (2022). *Systems Science: Theory, Analysis, Modeling, and Design.* Springer.
- Mobus, G.E. & Kalton, M.C. (2015). *Principles of Systems Science.* Springer.

### Primary Sources (Collaboration Targets)

- Joslyn, C. (1995). Semantic Control Systems. *World Futures* 45, 87–123.
- Joslyn, C. & Purvine, E. (2018). Seeking a Categorical Systems Theory via the Category of Hypergraphs. NIST Workshop on Applied Category Theory, PNNL-SA-133059.
- Mesarovic, M.D. (1964). Foundations for a General Systems Theory. In Mesarovic (ed.), *Views on General Systems Theory,* pp. 1–24. Wiley.
- Mesarovic, M.D. & Takahara, Y. (1975). *General Systems Theory: Mathematical Foundations.* Academic Press.

### Secondary Sources

- Ashby, W.R. (1956). *An Introduction to Cybernetics.* Chapman & Hall.
- Conant, R.C. & Ashby, W.R. (1970). Every Good Regulator of a System Must Be a Model of That System. *Int. J. Systems Science* 1(2), 89–97.
- de Moura, L. & Ullrich, S. (2021). The Lean 4 Theorem Prover and Programming Language. In *CADE-28.* Springer.
- Klir, G.J. & Valach, M. (1967). *Cybernetic Modelling.* Iliffe.
- Myers, D.J. (2023). *Categorical Systems Theory.* Draft.

---

*Document compiled 2026-04-19. Codebase includes Thermostat.lean (post-c944f42).*
*Formalization repository: systems-ontology (Lean 4 + Mathlib).*
