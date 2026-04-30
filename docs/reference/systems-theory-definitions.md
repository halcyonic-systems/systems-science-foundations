# Formal System Definitions: A Comparative Reference
## Mesarovic · Wymore · Klir · Bunge · Joslyn · Mobus

*Compiled for BERT formalization work and Lean 4 theorem development.*

---

## 0. Source Verification Status

*Last fact-check: 2026-04-20 against Zotero library + primary source OCR.*

### 0.1 Per-Definition Tracking Table

Legend: ✅ verified · ⚠️ discrepancy found · ❓ unverified (source missing) · 🔴 wrong attribution

| # | Claim / Definition | Section | Status | Source in Zotero? | Action |
|---|---|---|---|---|---|
| 1 | Mesarovic: `S ⊆ ×{Vᵢ: i ∈ I}` relational definition | §3 | ✅ verified 2026-04-20 | ✅ M&T 1975 (ZA3E2PD3), OCR Ch.II Def 1.1 (p.11) | Notation was `∏ Fᵢ`; corrected to M&T's `×{Vᵢ: i ∈ I}` |
| 2 | Mesarovic: elementary I/O system `S ⊂ V × Y` | §3 | ✅ verified 2026-04-20 | ✅ M&T 1975 Def 1.2 (p.11) | Was `S ⊆ I × O`; M&T use V (input) and Y (output), strict subset ⊂ |
| 3 | Mesarovic: non-elementary composition via internal `M` | §3 | ❓ not in Ch.II | ✅ M&T 1975 in Zotero | May be in Ch.X "Interconnections"; Ch.II has global state (Def 1.4) not coupling |
| 4 | Mesarovic: decomposition theorem (n > 2 ⇒ internal states) | §3, §8 | ⚠️ citation error | ✅ M&T 1975 in Zotero; also Joslyn 1995 cites Mesarovic 1964 p.14 | Cite **Mesarovic 1964, p. 14** — not M&T 1975 |
| 5 | Mesarovic & Takahara publication date 1989 | §3, §13 | ⚠️ possibly wrong | ✅ M&T 1975 in Zotero | Joslyn cites **1988 Springer**; verify correct date for *Abstract Systems Theory* |
| 6 | Wymore: core system model as quintuple `Z = (S, I, O, N, R)` | §4 | ✅ verified 2026-04-20 | ✅ Wach et al. 2021 (BNPE2684) Appendix B, Eq A1 citing T3SD [20] | Was "7-tuple `⟨T, X, Ω, Y, Q, δ, λ⟩`"; T3SD base is a **quintuple** (S=states, I=inputs, O=outputs, N=next-state, R=readout). Time+initial-state added at FSD level: `FSD = (Z, DS_Z, TS_Z)` |
| 7 | Wymore: semigroup constraint on δ | §4 | ❓ not verified in Wach et al. | ✅ Wach et al. in Zotero | Wach et al. describe Moore-machine basis but don't state semigroup explicitly; may be in Wymore 1967 directly |
| 8 | Wymore: T3SD tricotyledon (functionality/buildability/implementability) | §4 | ✅ verified 2026-04-20 | ✅ Wach et al. 2021 §3.1 | FSD/BSD/ISD spaces confirmed with metamodel |
| 9 | Wymore: coupling theory / closure under coupling | §4, §10 | ✅ partial 2026-04-20 | ✅ Wach et al. 2021 §3.1 | System Coupling Recipe (SCR) confirmed in metamodel |
| 10 | Klir: epistemological hierarchy (source→data→generative→structure→metasystem) | §5 | ✅ verified | ✅ *Facets* (1991) YRQKD6Q9 | — |
| 11 | Klir: Level 0 "Background" as unstructured phenomena | §5 | ❓ unverified | ✅ *Facets* has levels but Level-0 naming unclear | Verify against Klir 1985 *Architecture* |
| 12 | Klir: `G = ⟨V, R⟩` generative-system form | §5 | ❓ unverified in *Facets* | ✅ *Facets* only | **Acquire Klir 1985** for canonical statement |
| 13 | **Bunge: CESM 4-tuple `⟨C, E, S, M⟩` in 1979** | §6 | 🔴 **WRONG attribution** | ✅ *Treatise* (1979) QTHMLVUZ | **Bunge 1979 defines TRIPLE `⟨C, E, S⟩`** — re-cite to Bunge 2000 *Systemism* or 2003 *E&C* |
| 14 | Bunge: "mechanism as modus operandi" phrasing | §6 | ⚠️ in wrong source | ✅ Systemism (2000) SQNJMPL3 has it | Move citation from 1979 → 2000 |
| 15 | Bunge: emergence defined mechanistically | §6 | ❓ partial | ✅ 1979 + Systemism 2000 | Acquire *Emergence and Convergence* (2003) for full claim |
| 16 | **Mobus: "less set-theoretic" / stocks-flows-only framing** | §7 | 🔴 **WRONG characterization** | ✅ *Principles* (2015) QFSYTLNG | **Mobus defines 6-tuple `{C, N, I, B, K, H}ₗ`** (Quant Box 3.1/10.1) — rewrite §7 |
| 17 | Mobus: CESM correspondence (comp/env/structure/mechanism) | §7 | ⚠️ imprecise | ✅ | Replace with explicit 6-tuple mapping |
| 18 | Myers Def 1.2.1.2: deterministic system as 5-tuple | §9 | ✅ structurally verified | ✅ 5HVAGR5N | Note Myers writes it diagrammatically `(State,State)⇆(In,Out)`, not as 5-tuple |
| 19 | Myers Def 1.3.1.1: lens `(f, f♯)` passforward/passback | §9 | ✅ verified verbatim | ✅ | — |
| 20 | Myers: Moore-machine identification (Remark 1.2.1.3) | §9 | ✅ verified | ✅ | — |
| 21 | Myers: compositionality theorem (Ch. 5, representable lax doubly indexed functors) | §9 | ❓ not verified in depth | ✅ | Read Myers Ch. 5 to verify theorem statement |
| 22 | Myers: "only account that proves general compositionality theorem" | §2.5 | ⚠️ possibly overstated | ✅ Myers; 🆕 Takahara & Takai 1985 may be prior art | **Investigate Takahara & Takai 1985** "Category Theoretical Framework of General Systems" |
| 23 | Joslyn Def 5: system as `S ⊆ ∏ Xᵢ`, `S ≠ ∅` | §8 | ✅ verified verbatim | ✅ Semantic Control (1995) JXTBBK89 | — |
| 24 | Joslyn Def 6: constraint `C := X − S` | §8 | ✅ verified | ✅ | — |
| 25 | Joslyn Defs 17/18: dimensional / cardinal variety | §8 | ✅ verified | ✅ | — |
| 26 | Joslyn Def 21: "cardinal distinction on a variety of dimensional distinctions" | §8 | ✅ verified verbatim | ✅ | — |
| 27 | Joslyn Prop 29: "control₂ requires internal states" | §8 | ⚠️ imprecise | ✅ | Actual: "O is itself a control₁ system `(Oₑ, Oᵢ)`" — tighten wording |
| 28 | Joslyn: rule vs. law → semantic relation argument | §8 | ✅ verified | ✅ | — |
| 29 | Joslyn: afferent-efferent loop structure | §8 | ✅ verified | ✅ | — |
| 30 | **"Joslyn not category-theoretic"** | §2.1, §8 | ⚠️ true of 1995, dated overall | ✅ Also have Joslyn & Purvine (2018) LK5S5GWZ | Narrow claim to 1995 paper; note 2018 categorical-hypergraph direction |
| 31 | Joslyn/Heylighen/Turchin 1993 Principia Cybernetica Synopsis | §8, §13 | ❓ unverified | ❌ | Acquire or mark as "cited from secondary" |

### 0.2 Missing Primary Sources — Acquisition Priority

| Priority | Source | Blocks verification of | Strategy |
|---|---|---|---|
| **P0** | Mesarovic, M.D. (1964) *Views on General Systems Theory* | Decomposition theorem (p.14); Joslyn's primary Mesarovic citation | Library ILL / archive.org scan |
| ~~P0~~ | ~~Mesarovic & Takahara (1975)~~ | ~~§3 full theory~~ | ✅ **ACQUIRED** 2026-04-20 in Zotero (ZA3E2PD3, 48pp scan). Ch.II Defs 1.1-1.4 verified via OCR. |
| **P0** | Wymore, A.W. (1967) *A Mathematical Theory of Systems Engineering* | Semigroup constraint; Ω as function space; original 7-tuple form if different from T3SD quintuple | Library ILL |
| ~~P1~~ | ~~Wymore, A.W. (1993)~~ *Model-Based Systems Engineering* | ~~§4 T3SD~~ | ✅ **Wach et al. (2021)** BNPE2684 provides T3SD metamodel + core equations. Primary source still valuable but not blocking. |
| **P1** | Bunge, M. (2003) *Emergence and Convergence* | §6 CESM + emergence (currently mis-cited to 1979) | Library ILL |
| **P1** | Klir, G.J. (1985) *Architecture of Systems Problem Solving* | §5 canonical hierarchy | Have Facets (1991); add this for rigor |
| **P2** | Mesarovic & Takahara (1988/1989) *Abstract Systems Theory* | §3 abstract framework; verify year | Springer; verify 1988 vs 1989 |
| **P2** | Klir, G.J. (1969) *An Approach to General Systems Theory* | §5 foundational | Library ILL |
| **P2** | Joslyn, Heylighen & Turchin (1993) Principia Cybernetica Synopsis | §8 secondary Joslyn claims | PC Project site / Brussels proceedings |
| **P2** | 🆕 Takahara & Takai (1985) "Category Theoretical Framework of General Systems," *Int. J. General Systems* 11:1 | **NOT CURRENTLY CITED** but may be prior art weakening Myers uniqueness claim | Journal access |
| P3 | Bunge, M. (2004) "How does it work? The search for explanatory mechanisms" | Alternative source for "modus operandi" | Journal access |

### 0.3 Required Corrections (Before Citing This Doc Elsewhere)

1. **§6 Bunge CESM** — Re-cite to Bunge (2000) *Systemism* (Zotero: SQNJMPL3) or Bunge (2003) *Emergence and Convergence*. The 1979 *Treatise* defines the **triple** `⟨C, E, S⟩` only. Verified quote from 1979 p. 6: *"the ordered triple ⟨C, E, S⟩ is (or represents) a system over T."* Bunge 2000 *Systemism* abstract adds: "Concrete systems...are also characterized by their mechanism or modus operandi."
2. **§7 Mobus** — Rewrite to present the **6-tuple `Sₗ = {C, N, I, B, K, H}ₗ`** from Mobus & Kalton 2015 Quant Box 3.1/10.1. Remove "less set-theoretic" framing. Stocks-and-flows is pedagogical, not definitional.
3. **§8 Joslyn Prop 29** — Change "requires internal states" to the precise form: *"O is itself a control₁ system `O = (Oₑ, Oᵢ)`."* The stronger claim matters for the metasystem cascade.
4. **§2.1 / §8 Joslyn + category theory** — Narrow the "not category-theoretic" claim explicitly to the 1995 paper. Add cross-reference to Joslyn & Purvine (2018) "Seeking a Categorical Systems Theory via the Category of Hypergraphs" (Zotero: LK5S5GWZ).
5. **§2.5 Myers uniqueness** — Qualify the compositionality-theorem-uniqueness claim pending review of Takahara & Takai (1985).
6. **§3, §8 Mesarovic decomposition theorem** — Cite to **Mesarovic (1964), p. 14** (per Joslyn 1995). Current document implies M&T; Joslyn's actual citation is the 1964 solo volume.
7. **§13 Bibliography** — Verify Mesarovic & Takahara second-book date: document says 1989, Joslyn 1995 cites 1988.

---

## 1. Overview and Motivation

The systems science literature contains several distinct set-theoretic system definitions that are not competing so much as *layered* — each capturing a different level of abstraction or ontological commitment. No single definition has been universally adopted by the systems community. This document surveys the principal definitions relevant to BERT's formal grounding and a Lean 4 formalization project, and maps the structural relationships between them.

The four levels of commitment, from least to most:

| Level | Stance | Primary Theorist(s) |
|---|---|---|
| **Extensional / Behavioral** | A system *is* its input-output relation | Mesarovic & Takahara |
| **Operational / State-based** | A system *is* the mechanism producing that relation | Wymore |
| **Epistemological / Variable-based** | A system *is* a structured reconstruction from observed traits | Klir |
| **Ontological / Mechanistic** | A system *is* a thing with composition, environment, structure, and mechanism | Bunge (CESM); Mobus |
| **Compositional / Categorical** | A system *is* a lens — a typed interface with bidirectional information flow, composable via wiring diagrams | Myers |
| **Semiotic / Variety-theoretic** | A system *is* a cardinal distinction on a variety of dimensional distinctions; control requires rule-following (semantic) relations | Joslyn |

Joslyn sits closest to Mesarovic mathematically but adds the classical/constructivist synthesis, a taxonomy of system types, and the argument that control₂ systems necessarily contain semantic relations. Myers provides the categorical / compositional layer that makes the whole stack formally interoperable.

---

## 2. Classification by Mathematical Type, Motivation, and Problem Orientation

### 2.1 Mathematical Type

| Theorist | Mathematical Type | Primary Formalism |
|---|---|---|
| **Mesarovic** | Set-theoretic relational | `S ⊆ ∏ Xᵢ` — system as relation on Cartesian product |
| **Wymore** | Set-theoretic operational / automata-theoretic | 7-tuple with explicit time set, admissible input function space, state transition |
| **Klir** | Set-theoretic / information-theoretic | Variables, trait structures, constraint; reconstructability via uncertainty measures |
| **Bunge** | Mereological / ontological | CESM 4-tuple with realist commitments to parts, relations, mechanisms |
| **Mobus** | Process-network / graph-theoretic | Stocks, flows, feedback topology; causal graph over physical quantities |
| **Myers (Set)** | Set-theoretic operational | Deterministic system as 5-tuple; structurally identical to Wymore at a single time step |
| **Myers (general)** | Category-theoretic / functorial | Lenses in any cartesian category; systems as objects in `Lens_C`; compositionality via double categories |
| **Joslyn** | Set-theoretic / variety-theoretic / cybernetic | Mesarovic base extended with dimensional/cardinal variety axes; constraint as set subtraction; control as constraint reduction |

**Notes on the Myers split**: Myers's *definition* of a deterministic system is set-theoretic (identical in structure to Wymore in Set). The category-theoretic machinery enters when he lifts the definition to an arbitrary cartesian category C and proves compositionality via functorial constructions. The two levels are cleanly separable — you can use Myers's system definition without the category theory, but the compositionality theorem requires it.

**Notes on Joslyn**: The paper uses directed arrows `A → B` for functional relations, but in the standard mathematical sense of functions between sets, not categorical morphisms. No functors, natural transformations, or limits appear. Joslyn's formalism is Mesarovic + Ashby cybernetics (variety, constraint, requisite variety) + Peircean semiotics. It is not category-theoretic.

---

### 2.2 Motivation / Research Program

| Theorist | Primary Motivation | Secondary Motivation |
|---|---|---|
| **Mesarovic** | Pure mathematical foundations of GST — rigorous axiomatic theory of systems in full generality | Unification of engineering systems theory across domains |
| **Wymore** | Mathematical foundations of systems engineering — formalizing SE practice | Hybrid systems; systems including humans, machines, and software |
| **Klir** | Epistemology and uncertainty — what can be known about a system from observational data | Reconstructability analysis; uncertainty-based information theory |
| **Bunge** | Scientific ontology — what systems really are, independently of observers | Integration of systems thinking with philosophy of science and realism |
| **Mobus** | Applied pedagogy and physical intuition — teaching systems science | Computational modeling of real-world complex systems |
| **Myers** | Compositionality and modularity — how systems combine and how behaviors of composites relate to components | Unification of disparate systems theories under a common categorical framework |
| **Joslyn** | Cybernetics and control — grounding the concepts of control and metasystem transition in rigorous systems-theoretic terms | Biosemiotics — the argument that control₂ systems necessarily involve semantic relations |

---

### 2.3 Problem Orientation

| Problem Type | Question | Theorist(s) |
|---|---|---|
| **Forward** | Given a system definition, what behavior does it produce? | Wymore, Myers, Mobus |
| **Inverse / Identification** | Given observed behavior or data, what system generated it? | Klir |
| **Ontological** | What *is* a system — what are its real constituents? | Bunge |
| **Compositional** | How do systems combine, and what can be said about composite behavior from component behavior? | Myers (compositionality theorem), Wymore (coupling theory) |
| **Control-theoretic** | What conditions are required for a system to maintain a variable against disturbance? | Joslyn |
| **Semantic** | What kind of functional relation inhabits a system — rule or law — and what does this imply about meaning? | Joslyn |
| **Agnostic / Doctrine-relative** | All of the above, depending on which doctrine is chosen | Myers (doctrine framework) |

---

### 2.4 Ontological Stance

| Theorist | Stance | Commitment |
|---|---|---|
| **Mesarovic** | Extensional | A system is identified with its I/O relation — no ontological commitment to what produces it |
| **Wymore** | Operational | A system is identified with the mechanism producing behavior — state set and transition function are real |
| **Klir** | Epistemological | Systems are reconstructions from observations; what exists is always relative to the observational frame |
| **Bunge** | Scientific realist | Systems are real things with real parts, real relations, and real mechanisms, independent of observers |
| **Mobus** | Realist / pragmatic | Follows Bunge; physical processes and stocks/flows are real; models track real causal structure |
| **Myers** | Agnostic | Doctrine-relative; ontological commitments are parameters of the doctrine, not of the theory itself |
| **Joslyn** | Synthetic | Bridges classical realism (cardinal constraints are objective) and constructivism (dimensional distinctions are observer-acts); neither rejected |

---

### 2.5 Unique Contribution of Each Definition

| Theorist | What No Other Definition Provides |
|---|---|
| **Mesarovic** | The most general and parsimonious base. The decomposition theorem (systems of dimension > 2 require internal states) is a foundational result not derived elsewhere. |
| **Wymore** | Admissible input function space `Ω` as a first-class component — time and trajectory structure are explicit. Coupling theory with closure proofs. Subsumes Turing machines, sequential machines, and ODEs in one definition. |
| **Klir** | The only full account of *inverse* system identification. Epistemological hierarchy from raw observation to structural explanation. Integration of uncertainty measures into systems theory. |
| **Bunge** | The only account that includes *mechanism* as an ontological primitive — not just what a system does or is made of, but how it works causally. Emergence defined precisely in mechanistic terms. |
| **Mobus** | The only account grounded in physical process quantities (stocks, flows). The strongest alignment with system dynamics and simulation practice. The only one with a developed pedagogy. |
| **Myers** | The only account that proves a general *compositionality theorem* — behaviors of composite systems computed from component behaviors. Lens identification makes composition a first-class mathematical operation. Doctrine framework is the only meta-level account of why definitions differ. |
| **Joslyn** | The only account of what *kind* of functional relation inhabits a system (rule vs. law) and what this implies about meaning. The only two-axis taxonomy of system types. The only bridge from control theory to biosemiotics through systems-theoretic argument. |

---

## 3. Mesarovic & Takahara — Abstract Systems Theory (AST)

### Core Definition

A **system** is defined as a relation on abstract sets:

```
S ⊆ ∏_{i ∈ J} Fᵢ
```

where the sets `Fᵢ` are called *objects* of the system. Each `Fᵢ` represents the totality of all appearances of (or experiences with) an attribute of the real-life phenomena under consideration.

**Input-output (elementary) system** — the canonical special case:

```
S ⊆ I × O
```

where `I` is the input set and `O` is the output set.

- The input set consists of objects representing influence *from* the environment on the system.
- The output set consists of objects representing influence *from* the system on the environment.

**Non-elementary (structured) system** — composed of two coupled elementary systems:

```
S ⊆ I × O   composed from   S₁ ⊆ (I × O) × M   and   S₂ ⊆ (M × I) × O
```

where `M` is an internal mediating set.

### Key Properties

- **Ontological stance**: Extensional. The system *is* the relation — not a thing that *has* a relation.
- **Time**: Absent from the base definition. Introduced separately via time-indexed object sets.
- **State**: Not a primitive. State is a derived or imposed concept.
- **Causality**: Not inherent; the I/O relation is atemporal.
- **Formalization approach**: Top-down axiomatic; starts from abstract sets and derives systems properties algebraically.

### Theoretical Scope

Mesarovic & Takahara develop a full theory of:
- **Realization**: When does an abstract I/O relation have a state-space realization?
- **Decomposition**: Hierarchical and modular system structure.
- **Goal-seeking systems**: Systems with preferred output subsets.
- **Time systems**: Adding a time base `T` to the abstract relation framework.

### Works

- Mesarovic, M.D. (1964). *Views on General Systems Theory*. Wiley.
- Mesarovic, M.D. & Takahara, Y. (1975). *General Systems Theory: Mathematical Foundations*. Academic Press. (Mathematics in Science and Engineering, Vol. 113.)
- Mesarovic, M.D. & Takahara, Y. (1989). *Abstract Systems Theory*. Springer. (Lecture Notes in Control and Information Sciences, Vol. 116.)

---

## 4. Wymore — Mathematical Theory of Systems Engineering (T3SD)

### Core Definition

A **system** is a 7-tuple (in the 1967 formulation):

```
Σ = ⟨T, X, Ω, Y, Q, δ, λ⟩
```

| Component | Symbol | Description |
|---|---|---|
| Time set | `T` | Ordered set; nonneg reals ℝ⁺ or integers ℤ⁺ |
| Input value set | `X` | Set of all possible input values |
| Admissible input functions | `Ω ⊆ (T → X)` | Function space of allowable input trajectories |
| Output value set | `Y` | Set of all possible output values |
| State set | `Q` | Set of all possible system states |
| State transition function | `δ : Q × Ω → Q` | Maps (state, input segment) to next state |
| Readout / output function | `λ : Q → Y` | Maps state to output (Moore-type) |

Constraints on `δ`:
1. The identity function `ω` (null input segment) is in `Ω` and `δ(q, ω) = q` for all `q ∈ Q`.
2. Composition of input segments corresponds to composition of transitions (semigroup property).

This is essentially a **generalized Moore machine over continuous or discrete time**, with the admissible input function space `Ω` as a first-class mathematical citizen.

### Key Properties

- **Ontological stance**: Operational. The system *is* the mechanism producing behavior — the transition function and state space underneath the I/O relation.
- **Time**: Explicit, typed, and first-class (`T` is a required component).
- **State**: Explicit primitive (`Q`).
- **Dynamics**: State-transition based; encompasses Turing machines, sequential machines, and ODE-based systems as special cases.
- **Input**: Not just a set but a *function space* `Ω` — captures temporal trajectory structure, not just instantaneous values.

### Scope and Extensions

In *Model-Based Systems Engineering* (T3SD, 1993), Wymore extends this to a **Tricotyledon Theory of System Design** with three spaces:
- **Functionality space**: What the system must do (I/O requirements)
- **Buildability space**: What technologies can implement it
- **Implementability space**: The set of designs that satisfy both

T3SD also develops:
- **System coupling**: Formal composition with feedback loops; conditions for closure under coupling within `SYSTEMS`
- **Homomorphisms**: Structure-preserving maps between system models (isomorphisms, equivalences)
- **Requirements formalization**: Mathematical input/output requirement structures

### Works

- Wymore, A.W. (1967). *A Mathematical Theory of Systems Engineering: The Elements*. Wiley.
- Wymore, A.W. (1993). *Model-Based Systems Engineering*. CRC Press.

---

## 5. Klir — General Systems Problem Solver / Reconstructability Analysis

### Core Definition

Klir's approach is epistemological rather than ontological: a system is a structured reconstruction from observed variables and their relationships.

**Source system**: A set of variables `{V₁, V₂, ..., Vₙ}` observed over a base set (often time).

**Data system**: An assignment of observed state-tuples from the Cartesian product of variable ranges — the empirical record.

**Generative system**: A system that can reproduce the data system — the minimal structure sufficient to explain observed behavior.

**Structure system**: Specification of which variables are coupled (the *support* of the relation).

Formally, a system at the "generative" level is characterized by:

```
G = ⟨V, R⟩
```

where `V = {V₁, ..., Vₙ}` is a set of variables (each with a range set `Sᵢ`) and `R ⊆ S₁ × S₂ × ... × Sₙ` is the constraint relation on their joint state space.

Klir's **epistemological hierarchy** (from raw observation to structural explanation):

| Level | Name | Content |
|---|---|---|
| 0 | Background | Unstructured phenomena |
| 1 | Source system | Named variables, ranges |
| 2 | Data system | Observed state tuples |
| 3 | Generative system | State-transition structure |
| 4 | Structure system | Coupling topology |
| 5 | Meta-system | System of systems |

### Key Properties

- **Ontological stance**: Epistemological. Systems are *reconstructed from observations*, not postulated from ontology.
- **Reconstructability analysis**: Given a data system, find the minimal structure system that can reproduce it — an inverse problem.
- **Uncertainty**: Klir integrates information theory and uncertainty measures (possibility theory, probability) into the framework.

### Works

- Klir, G.J. (1969). *An Approach to General Systems Theory*. Van Nostrand Reinhold.
- Klir, G.J. (1985). *Architecture of Systems Problem Solving*. Plenum.
- Klir, G.J. (1991). *Facets of Systems Science*. Plenum.

---

## 6. Bunge — CESM Ontology

### Core Definition

A **system** is a 4-tuple:

```
σ = ⟨C, E, S, M⟩
```

| Component | Symbol | Description |
|---|---|---|
| Composition | `C` | The set of parts (entities constituting the system) |
| Environment | `E` | The set of entities outside the system that interact with it |
| Structure | `S` | The set of relations (bonds, interactions) among `C` and between `C` and `E` |
| Mechanism | `M` | The set of processes by which the system functions and changes |

All four components are required. A system with no mechanism is a *static structure*, not a system. A system with no structure is merely a collection.

### Key Properties

- **Ontological stance**: Scientific realist. Systems are real things existing independently of observers, with real parts, real relations, and real mechanisms.
- **Composition** is always specific entities — not abstract sets or variable ranges.
- **Environment** is explicitly modeled as a first-class component, not merely "everything outside."
- **Mechanism** is what Bunge calls the *modus operandi* — the causal processes that produce the system's behavior. This distinguishes CESM from purely structural or behavioral definitions.
- **Emergence**: Bunge defines emergence precisely in terms of properties of the whole not present in the parts — derivable from M acting on C under S.

### Relation to Other Definitions

- Mesarovic's `I × O` corresponds to `E` (environment interface) in CESM.
- Wymore's `Q` and `δ` correspond to `M` (mechanism) in CESM.
- Wymore's `S` (structure topology) corresponds to Bunge's `S`.
- Klir's variables correspond to projections of Bunge's `C` attributes.

### Works

- Bunge, M. (1979). *Treatise on Basic Philosophy, Vol. 4: Ontology II: A World of Systems*. Reidel.
- Bunge, M. (2000). "Energy: Between Physics and Metaphysics." *Science & Education*.
- Bunge, M. (2003). *Emergence and Convergence*. University of Toronto Press.

---

## 7. Mobus — Systems Science Formalism

### Core Definition

Mobus (following the systems science tradition of Bertalanffy and Bunge) treats a system as fundamentally a **process network** — entities in causal interaction over time, organized hierarchically.

Key primitives:
- **System boundary**: Explicit demarcation of inside/outside
- **Stocks and flows**: Conserved quantities and their rates of change (following Forrester/system dynamics)
- **Feedback loops**: Causal circuits (positive/negative)
- **Hierarchy**: Systems composed of subsystems, embedded in supersystems

The definition is less purely set-theoretic than Mesarovic or Wymore, and more aligned with Bunge's CESM extended with explicit process semantics and hierarchy.

### Key Properties

- Mobus grounds systems science pedagogy in both formalism and physical intuition.
- His formalism explicitly maps to Bunge's CESM: composition = entities; environment = boundary crossing; structure = feedback topology; mechanism = causal processes.
- Strong alignment with BERT's modeling philosophy.

### Works

- Mobus, G.E. & Kalton, M.C. (2015). *Principles of Systems Science*. Springer.

---

## 8. Joslyn — Variety-Theoretic / Semiotic Systems

### Mathematical Basis

Joslyn's formal apparatus is **set-theoretic**, working squarely within the Mesarovic tradition. The foundational definition is identical to Mesarovic's: a system is a relation `S ⊆ X = ∏ Xᵢ` on a finite family of sets. The distinctive formal contribution is the decomposition of variety into two orthogonal axes — **dimensional** and **cardinal** — and the derivation of a taxonomy of system types from their interaction.

### Core Definitions

**System (Mesarovic-style base, Def. 5):**

```
Given sets X₁, ..., Xₙ with X := ∏ Xᵢ,
a system S is any relation S ⊆ X, S ≠ ∅
```

**Constraint (Def. 6):**

```
C := X - S     (set subtraction)
```

The constraint `C` represents the states `X` cannot achieve — the functional or structural properties of `S` as a whole.

**Dimensional variety (Def. 17):** The number of distinct dimensions `n`.

**Cardinal variety (Def. 18):** The cardinality `|S|` of the system, bounded by `1 ≤ |S| ≤ |X|`.

**Constraint₂ (Def. 15):** The *reduction* of variety — a dynamic sense of constraint as act, not just state.

### Taxonomy of System Types

Joslyn derives a 2×2 classification from the interaction of dimensional and cardinal variety:

| | `n = 1` (no dim. variety) | `n > 1` (some dim. variety) |
|---|---|---|
| `S = X` (no cardinal constraint) | Simple Set (A) | Aggregate (B) |
| `S ⊊ X` (some cardinal constraint) | Simple Distinction (C) | **Proper System (D)** |

Only case (D) — multiple dimensions with non-trivial constraint — constitutes a *proper system*. This is not merely terminological: Joslyn argues that cases (A), (B), and (C) have serious problems as systems in any full sense.

### The Synthetic System Definition

Joslyn's deepest contribution is the **classical/constructivist distinction** (Section 2.1) and the synthetic resolution:

- **Classical (structuralist) view**: A system is an objective set of objects and relations — Mesarovic's `S ⊆ X`. Systems exist independently of observers.
- **Constructivist (functionalist) view**: A system is a bounded region distinguished by an observer — the act of drawing a distinction (Goguen & Varela, Spencer-Brown). Dimensions are not given *a priori* but created by distinction-making.

The resolution turns on a type/token distinction: **dimensions correspond to logical types** (cardinal variety presupposes dimensional variety; you cannot constrain what has not first been dimensionally distinguished). Dimensional distinctions are nonprocedural and open-ended (no complement can be constructively specified); cardinal distinctions are Boolean and complemented (`S ∪ C = X`, `S ∩ C = ∅`).

**Synthetic Definition (Def. 21):**

> *A system is a cardinal distinction on a variety of dimensional distinctions.*

This is more informative than Mesarovic's bare relation: it specifies the *origin* of the dimensions (acts of distinction-making, which are constructivist) and the *nature* of the system boundary (a cardinal constraint on those dimensions, which is classically Boolean).

### The Metasystem and Systemic Stance

Every system `S ⊆ X` generates a **contingent metasystem** `S' := ⟨S, E⟩` where `E` is the system's environment (identified with constraint `C`). This introduces a hierarchy: every system can be regarded as a part of the metasystem formed by itself and its environment.

The **systemic stance** — treating a part in the context of its environmental interactions rather than in isolation — is explicitly analogous to Dennett's intentional stance. Joslyn cites Salthe's hierarchy theory: every true hierarchical level requires a *ternary* distinction (level below, this level, level above), not merely binary.

### Semantics and Control

The paper's central argument connects formal systems theory to semiotics via control theory:

**Control₁**: Passive constraint — a stable equilibrium where parameters do not vary. The ball rolls to the bottom of the valley.

**Control₂**: Active control — the controlled variable remains stable *despite* environmental variation. The equilibrium is maintained against disturbances by compensating internal activity.

The key theorem (Proposition 29): Control₂ requires the controlled system `O` to have **internal states** — a result derived directly from Mesarovic's decomposition theorem (a system of dimension > 2 cannot in general be expressed as a product of 2-fold input-output systems). The internal controller `Oₑ` and internal variables `Oᵢ` form an **afferent-efferent loop**.

The semiotic argument: the feedback function `f : Oᵢ → Oₑ` must be a *rule* (contingent entailment), not a natural law. Rules are arbitrary, conventional, and selected — exactly the properties of Peircean signs. Therefore:

> A system which has contingent entailments (rules) contains **semantic relations** among its components.

And therefore control₂ systems necessarily involve semantics. Since living systems require control₂ (homeostasis, regulation against disturbance), living systems necessarily involve semantic relations — the biosemiotic thesis.

### Key Properties

- **Ontological stance**: Synthetic — bridges classical (realist, structural) and constructivist (observer-relative, functional) views. Neither rejects the other; each applies to a different aspect (cardinal vs. dimensional variety).
- **Mathematical type**: Set-theoretic / variety-theoretic. The formal machinery is Mesarovic's relation-on-sets framework, extended with cardinality/dimensionality analysis and cybernetic constraint theory.
- **Motivation**: Cybernetics and systems science (Principia Cybernetica Project). Primary concern is grounding the concept of control and the metasystem transition in rigorous systems-theoretic terms, then connecting this to biosemiotics.
- **Relation to Mesarovic**: Extends Mesarovic's structural view by analyzing the internal structure of the dimension set (type vs. token), deriving a taxonomy of system types, and providing a constructivist complement.
- **Relation to Klir**: Shares the variable/trait-based orientation; where Klir focuses on epistemological reconstruction from data, Joslyn focuses on the ontological and semiotic conditions for control and meaning.
- **Relation to Bunge**: The metasystem `⟨S, E⟩` anticipates Bunge's CESM environment component `E`; the systemic stance corresponds to considering a system's cross-boundary relations `S|_{C×E}`.
- **Not category-theoretic**: The paper uses directed arrows (`A → B`) for functional relations, but in the standard mathematical sense of functions between sets — not as morphisms in a category. No categorical machinery (functors, natural transformations, limits) is employed.

### Works

- Joslyn, C. (1995). "Semantic Control Systems." *World Futures*, 45, 87–123. (Principia Cybernetica Project, NASA Goddard Space Flight Center.)
- Joslyn, C., Heylighen, F. & Turchin, V. (1993). "Synopsis of the Principia Cybernetica Project." *Proc. 13th International Congress on Cybernetics*. Namur, Belgium.

---

## 9. Myers — Categorical Systems Theory (Dynamical Book, 2023)

### Core Position

David Jaz Myers's *Categorical Systems Theory* (draft, 2023) sidesteps the question of what a system *is* in general, and instead focuses on how systems **interact** — through interfaces, composition patterns, and wiring diagrams — using category theory as the organizing language. The book is dedicated to Bill Lawvere and draws on lens theory, double categories, and polynomial functors.

The key meta-level insight: rather than giving a single definition of system, Myers defines a **doctrine** — a structured answer to a suite of questions about what a systems theory should be — and then works within specific doctrines.

### The Four Informal Core Definitions

**Doctrine of dynamical systems (Informal Def. 0.0.0.1):**
A doctrine packages answers to the following questions:
- What does it mean to be a system — states, behaviors, or structured parts?
- What is the interface of a system?
- How can interfaces be connected in composition patterns?
- How are systems composed through those patterns?
- What is a map between systems, and how does it affect interfaces?

**Dynamical system (Informal Def. 0.0.0.2 / Def. 1.2.1.2):**

> A dynamical system consists of: a notion of how things can be, called the **states**, and a notion of how things will change given how they are, called the **dynamics**. The dynamics may depend on free **parameters or inputs** from the environment, and we may expose particular **outputs** to the environment.

**Theory of dynamical systems (Informal Def. 0.0.0.3):**
A theory answers: What does it mean to be a state? How should output vary with state? Can inputs depend on outputs? What changes are possible? How does change vary with input?

**Behavior (Informal Def. 0.0.0.4):**
> A behavior of a dynamical system is a particular way its states can change according to its dynamics.

### Formal Definition: Deterministic System (Def. 1.2.1.2)

A **deterministic system** `S` consists of:

```
S = ⟨State_S, Out_S, In_S, expose_S, update_S⟩
```

| Component | Type | Description |
|---|---|---|
| `State_S` | Set | The set of states |
| `Out_S` | Set | Values of exposed variables (outputs) |
| `In_S` | Set | Parameter values (inputs) |
| `expose_S` | `State_S → Out_S` | Readout / expose function |
| `update_S` | `State_S × In_S → State_S` | Dynamics / update function |

The **interface** of the system is the pair `(Out_S, In_S)`.

*Note*: Myers explicitly identifies this with a **Moore machine** (Remark 1.2.1.3). If `Out_S = {true, false}`, it reduces to a deterministic automaton. A start state is deliberately excluded from the definition.

This definition can be interpreted in **any cartesian category C**, not just Set — taking `State_S`, `Out_S`, `In_S` as objects and the functions as morphisms in C. This is how the differential systems case arises.

### Formal Definition: Differential System (Def. 1.2.2.1)

A **differential system** `S` with `n` state variables, `m` parameters, `k` exposed variables:

```
State_S = ℝⁿ,   In_S = ℝᵐ,   Out_S = ℝᵏ
expose_S : ℝⁿ → ℝᵏ        (smooth)
update_S : ℝⁿ × ℝᵐ → ℝⁿ  (smooth, gives derivatives)
```

The defining equations are: `ds_i/dt = update_S_i(s, i)` for each state variable.

This is a deterministic system interpreted in **Euc** — the cartesian category of Euclidean spaces and smooth maps.

### Systems as Lenses (Section 1.3)

The most structurally important insight in Myers: **a dynamical system is itself a lens**.

**Lens (Def. 1.3.1.1):** In a cartesian category C, a lens

```
(f, f♯) : (A⁻, A⁺) ⇆ (B⁻, B⁺)
```

consists of:
- A **passforward** map `f : A⁺ → B⁺` (downstream)
- A **passback** map `f♯ : A⁺ × B⁻ → A⁻` (upstream, using the current `A⁺` value)

**System as lens:** A deterministic system `S` is precisely the lens:

```
(update_S, expose_S) : (State_S, State_S) ⇆ (In_S, Out_S)
```

i.e., passforward = `expose_S : State_S → Out_S`, passback = `update_S : State_S × In_S → State_S`.

Deterministic systems are exactly the lenses whose input arena is of the form `(S, S)` — where both the "incoming" and "feedback" types are the same state set. This means:

- **Wiring diagrams are also lenses** (Section 1.3.3)
- **Composing systems = lens composition**
- The category **Lens_C** has arenas `(A⁻, A⁺)` as objects and lenses as morphisms

### Compositionality Theorem

Myers proves a general **compositionality theorem** (Chapter 5): behaviors of composite systems can be calculated from the behaviors of their components and the composition pattern. This is formalized as the construction of **representable lax doubly indexed functors**.

### Key Properties

- **Ontological stance**: Agnostic. Does not commit to what systems *are*; focuses on how they *interact* and *compose*.
- **Doctrine framework**: Meta-level — different doctrines give different systems theories (parameter-setting doctrine is the primary one; two others appear in Chapter 6).
- **Lens = system**: The identification of systems with lenses in a cartesian category is the central structural move.
- **Categorical generality**: Definitions interpret in any cartesian category — Set gives discrete/deterministic systems, Euc gives differential systems, other categories give other theories.
- **Compositionality first**: The theorems are primarily compositionality results; the definitions are organized to make composition well-behaved.

### Relation to Other Definitions

- Myers's deterministic system is structurally identical to **Wymore's system** (minus the explicit time set `T` and admissible function space `Ω`). Myers's `update_S` is Wymore's `δ`; `expose_S` is `λ`.
- The lens passback `f♯ : A⁺ × B⁻ → A⁻` generalizes **Mesarovic's I/O relation** into a functional, directional, compositional structure.
- The **arena** `(A⁻, A⁺)` is the categorical analog of **Bunge's boundary** — the typed interface through which a system meets its environment.
- The **doctrine** concept is Myers's answer to the lack of a universal definition that Mesarovic, Wymore, Klir, and Bunge each tried to solve differently.

### Works

- Myers, D.J. (2023). *Categorical Systems Theory*. Draft. (Book dedicated to Bill Lawvere; draws on joint work with David Spivak on polynomial functors.)

---

## 10. Structural Relations Between All Definitions

### Formal Mappings

**Wymore → Mesarovic** (behavior quotient):

Every Wymore system `⟨T, X, Ω, Y, Q, δ, λ⟩` induces a Mesarovic I/O relation:

```
S_M = { (ω, y) | ∃ q ∈ Q : y = λ(δ(q₀, ω)) }  ⊆  Ω × Y
```

The Mesarovic relation is the *behavioral quotient* of the Wymore system — it collapses all state-space information, retaining only observable I/O pairs.

**Myers ≅ Wymore** (structural equivalence, minus time):

Myers's deterministic system `⟨State, Out, In, expose, update⟩` is structurally identical to Wymore's system with `State = Q`, `expose = λ`, `update = δ`, but without Wymore's explicit time set `T` and admissible input function space `Ω`. Myers's system is a Wymore system at a single discrete time step, generalized to any cartesian category.

**Myers lens ⊇ Mesarovic** (generalization):

A Mesarovic I/O relation `S ⊆ I × O` is a special (non-functional, non-directional) case of a Myers lens. The lens makes the I/O relation functional (`f : A⁺ → B⁺`) and adds bidirectional structure (`f♯ : A⁺ × B⁻ → A⁻`). Lenses are the *functional, compositional refinement* of Mesarovic relations.

**Myers arena ↔ Bunge E boundary**:

Myers's arena `(A⁻, A⁺)` — the typed interface of a system — is the categorical realization of Bunge's environment boundary `S|_{C×E}`. The arena makes the boundary a first-class typed object with two directions.

**Non-injectivity (Wymore/Myers ↛ Mesarovic)**:

Multiple distinct Wymore/Myers systems (different state sets) can induce the same Mesarovic relation. The Mesarovic system underdetermines the operational mechanism. This is the classical *realization problem*.

**Wymore/Myers `⟨Q, δ⟩` ↔ Bunge M** (mechanism correspondence):

Wymore's `⟨Q, δ⟩` and Myers's `⟨State, update⟩` are the computational realization of Bunge's mechanism `M`. The state set encodes internal degrees of freedom; the transition/update function encodes causal rules.

**Klir ↔ Wymore Ω** (observation correspondence):

Klir's *data system* (observed variable trajectories) is the empirical correlate of Wymore's admissible input function space `Ω`. Klir asks: given trajectory data, what is the minimal generative system? Wymore asks: given a generative system, what `Ω` does it admit?

**Bunge E ↔ Mesarovic I/O**:

Bunge's environment component `E` and structure `S|_{C×E}` (cross-boundary relations) correspond to Mesarovic's `I × O`. The CESM boundary is the formal analog of Mesarovic's relation support.

**Myers doctrine ↔ The whole stack**:

Myers's *doctrine* concept is a meta-level answer to the lack of a universal definition. Each of Mesarovic, Wymore, Klir, and Bunge can be understood as instantiating a different doctrine — different answers to what states are, what interfaces are, and how composition works.

**Joslyn ↔ Mesarovic** (extension):

Joslyn's formal base is Mesarovic's `S ⊆ ∏ Xᵢ`. The extension is the two-axis analysis: dimensional variety (number of parts) and cardinal variety (`|S|` vs `|X|`), with constraint defined as `C := X - S`. The synthetic system definition (cardinal distinction on dimensional distinctions) is a more informative restatement of Mesarovic that adds the constructivist dimension-origin question.

**Joslyn classical/constructivist ↔ Bunge/Klir**:

Joslyn's classical view (systems as objective relational structures) maps to Bunge's realism. His constructivist view (systems as observer-drawn distinctions) maps to Klir's epistemological stance. His synthetic definition is an attempt to hold both simultaneously — dimensional distinctions are constructivist acts, cardinal constraints are classically Boolean once dimensions exist.

**Joslyn control₂ ↔ Wymore/Myers mechanism**:

Joslyn's control₂ system (active feedback maintaining a variable against disturbance) requires internal states — directly citing Mesarovic's decomposition theorem. This internal state requirement is the same structural insight that motivates Wymore's explicit state set `Q` and Myers's `State` component. Joslyn approaches it from the cybernetics/control side rather than the automata-theoretic side.

**Joslyn semantic relation ↔ rule vs. law**:

The semiotic contribution: functional relations in control₂ systems are *rules* (contingent, selected, arbitrary) not *laws* (necessary, discovered). This contingency is what makes them semiotic. This has no formal counterpart in Mesarovic, Wymore, Bunge, or Myers — it is Joslyn's unique contribution to the stack, addressing the question of *what kind of functional relation* inhabits a system.

### Summary Table

| Mapping | Direction | Content |
|---|---|---|
| Wymore → Mesarovic | Surjective (many-to-one) | I/O behavior is a quotient of state dynamics |
| Mesarovic → Wymore | Non-injective | Realization problem; many state systems, one relation |
| Myers ≅ Wymore | Structural equivalence | Same components, Myers drops explicit T/Ω, gains categorical generality |
| Myers lens ⊇ Mesarovic | Generalization | Lenses make I/O relations functional and bidirectional |
| Myers arena ↔ Bunge E | Boundary correspondence | Typed interface = CESM environment boundary |
| Wymore `⟨Q,δ⟩` ↔ Bunge `M` | Correspondence | State-based mechanism = computational realization of CESM mechanism |
| Klir data system ↔ Wymore `Ω` | Empirical grounding | Observed trajectories = admissible input function data |
| Mesarovic `I×O` ↔ Bunge `E ∩ S` | Boundary correspondence | I/O relation = cross-boundary structure in CESM |
| Myers doctrine | Meta-level | Packages the suite of questions each theorist answers differently |
| Joslyn ↔ Mesarovic | Extension | Adds dim/cardinal variety axes and synthetic definition to Mesarovic base |
| Joslyn classical/constructivist ↔ Bunge/Klir | Synthesis | Classical = Bunge realism; constructivist = Klir epistemology; Joslyn holds both |
| Joslyn control₂ ↔ Wymore/Myers state | Convergence | Internal states required for control₂ — same insight, different path |
| Joslyn semantic relation | Unique | Rule vs. law distinction — the only account in the stack of what kind of functional relation inhabits a system |

---

## 11. Application to BERT

BERT's formal system model is grounded primarily in **Bunge's CESM** as the ontological foundation, extended with Mobus's process semantics. The other definitions play supporting roles:

| Role in BERT | Theorist | Contribution |
|---|---|---|
| **Ontological core** | Bunge (CESM) | `⟨C, E, S, M⟩` as the system primitive |
| **Process semantics** | Mobus | Stocks, flows, feedback, hierarchy |
| **Boundary type / interface** | Mesarovic | I/O relation as formal interface specification |
| **Simulation substrate** | Wymore / Myers | `⟨Q, δ, λ⟩` / `⟨State, update, expose⟩` as operational semantics for Mesa/neuromorphic backends |
| **Observational grounding** | Klir | Variable structures for empirical system identification |
| **Composition & wiring** | Myers | Lens composition = BERT system coupling; arenas = typed interfaces; wiring diagrams = composition patterns |
| **System type taxonomy** | Joslyn | Proper system requires both dimensional AND cardinal variety — a constraint on BERT's system validity conditions |
| **Semantic grounding** | Joslyn | Rule vs. law distinction: BERT's update functions are rules (contingent, selected), not laws — this is what makes modeled systems genuinely semantic |

**BERT → TypeDB correspondence**: BERT's JSON models map to TypeDB's PERA model, with TypeDB owning `C + S`, boundary types owning `E` (Mesarovic I/O / Myers arena), and Mesa owning `M` (Wymore/Myers operational mechanism).

**Myers for BERT specifically**: The lens composition framework gives BERT's system coupling a rigorous categorical foundation. A BERT wiring diagram (connecting subsystems through their boundary types) is precisely a lens in the Myers sense. The compositionality theorem gives a formal guarantee that behaviors of wired BERT systems decompose into behaviors of their components.

---

## 12. Lean 4 Formalization Targets

The following theorems are the priority targets for Lean 4 formalization, ordered by dependency:

### Layer 1 — Base Definitions (Structures)
```lean
structure MesarovicSystem (I O : Type) where
  relation : Set (I × O)

structure WymoreSystem (T X Y Q : Type) where
  omega : Set (T → X)              -- admissible input functions
  delta : Q → (T → X) → Q         -- state transition
  lambda : Q → Y                   -- readout function

-- Myers deterministic system (= Wymore without explicit T/Ω)
structure MyersSystem (State In Out : Type) where
  expose : State → Out             -- expose_S
  update : State → In → State     -- update_S

-- Myers lens in a cartesian category (Set case)
structure Lens (Apos Aneg Bpos Bneg : Type) where
  passforward : Apos → Bpos
  passback    : Apos → Bneg → Aneg

structure BungeCESM (C E S M : Type) where
  composition  : Set C
  environment  : Set E
  structure_   : Set (C × C) × Set (C × E)
  mechanism    : Set M
```

### Layer 2 — Induced Behavior Maps
```lean
-- Every Wymore system induces a Mesarovic I/O relation
def wymoreToMesarovic {T X Y Q : Type}
    (q₀ : Q) (sys : WymoreSystem T X Y Q)
    : MesarovicSystem (T → X) Y :=
  { relation := { p | p.2 = sys.lambda (sys.delta q₀ p.1) } }

-- Every Myers system is a lens (system-as-lens identification)
def myersSystemAsLens {S I O : Type}
    (sys : MyersSystem S I O) : Lens S S I O :=
  { passforward := sys.expose
    passback    := fun s i => sys.update s i }

-- Myers system induces Mesarovic relation via expose ∘ update
def myersToMesarovic {S I O : Type}
    (s₀ : S) (sys : MyersSystem S I O)
    : MesarovicSystem I O :=
  { relation := { p | p.2 = sys.expose (sys.update s₀ p.1) } }
```

### Layer 3 — Key Theorems
1. **Behavioral quotient**: `wymoreToMesarovic` is well-defined and surjective onto the behavioral relation.
2. **Realization underdetermination**: Two Wymore/Myers systems with distinct state sets can induce equal Mesarovic relations. (State-bisimulation / behavioral equivalence.)
3. **Myers-Wymore equivalence**: `MyersSystem S I O` is equivalent to a single-step `WymoreSystem` — prove the isomorphism.
4. **System-as-lens**: `myersSystemAsLens` is a faithful embedding — Myers systems are exactly lenses whose input arena is of the form `(S, S)`.
5. **Lens composition preserves systems**: The composite of two system-lenses is a system-lens (closure under composition in `Lens_Set`).
6. **Mechanism correspondence**: Wymore/Myers `⟨Q, δ⟩` / `⟨State, update⟩` instantiates Bunge `M` — formalize as a functor between categories.
7. **CESM decomposition**: Every `BungeCESM` admits a Mesarovic / Myers arena interface on `E` — prove the boundary projection.
8. **Klir-Wymore data correspondence**: Observed trajectory sets in Klir's data system form a subset of Wymore's `Ω`.
9. **Compositionality** (Myers Ch. 5): Behaviors of composite systems (lens composites) decompose into behaviors of components. Formalize as a lax doubly indexed functor result.

### Layer 4 — BERT-Specific
- Prove that BERT's JSON schema types are sound instantiations of `BungeCESM`.
- Prove that the BERT→TypeDB transpiler preserves `C + S` components.
- Prove that boundary type interfaces satisfy both the Mesarovic I/O relation constraint and the Myers arena / lens structure.
- Prove that BERT's system coupling (wiring diagrams) is an instance of Myers lens composition.

---

## 13. Consolidated Reference List

### Primary Sources

- Bunge, M. (1979). *Treatise on Basic Philosophy, Vol. 4: Ontology II: A World of Systems*. Reidel.
- Bunge, M. (2003). *Emergence and Convergence: Qualitative Novelty and the Unity of Knowledge*. University of Toronto Press.
- Klir, G.J. (1969). *An Approach to General Systems Theory*. Van Nostrand Reinhold.
- Klir, G.J. (1985). *Architecture of Systems Problem Solving*. Plenum.
- Klir, G.J. (1991). *Facets of Systems Science*. Plenum.
- Mesarovic, M.D. (1964). *Views on General Systems Theory*. Wiley.
- Mesarovic, M.D. & Takahara, Y. (1975). *General Systems Theory: Mathematical Foundations*. Academic Press. (Mathematics in Science and Engineering, Vol. 113.)
- Mesarovic, M.D. & Takahara, Y. (1989). *Abstract Systems Theory*. Springer. (Lecture Notes in Control and Information Sciences, Vol. 116.)
- Mobus, G.E. & Kalton, M.C. (2015). *Principles of Systems Science*. Springer.
- Myers, D.J. (2023). *Categorical Systems Theory*. Draft. https://github.com/DavidJaz/DynamicalSystemsBook
- Von Bertalanffy, L. (1968). *General System Theory*. George Braziller.
- Wymore, A.W. (1967). *A Mathematical Theory of Systems Engineering: The Elements*. Wiley. (Repr. Robert E. Krieger, 1977.)
- Wymore, A.W. (1993). *Model-Based Systems Engineering: An Introduction to the Mathematical Theory of Discrete Systems and to the Tricotyledon Theory of System Design*. CRC Press.

### Secondary and Contextual Sources

- Albrecht, R. (1989). *Abstract Systems Theory*. Springer. (Encyclopedia of Mathematics survey.)
- Joslyn, C. (1995). "Semantic Control Systems." *World Futures*, 45, 87–123.
- Joslyn, C., Heylighen, F. & Turchin, V. (1993). "Synopsis of the Principia Cybernetica Project." *Proc. 13th International Congress on Cybernetics*, Namur, Belgium, 509–513.
- Mullin, A.A. (1975). Review of Mesarovic & Takahara (1975). *Bulletin of the American Mathematical Society*, 81(6), 1042–1044.
- Ören, T.I. & Zeigler, B.P. (2012). "System theoretic foundations of modeling and simulation: A historic perspective and the legacy of A. Wayne Wymore." *SIMULATION*, 88(9).
- Saleh, J.H. et al. (2021). "Conjoining Wymore's Systems Theoretic Framework and the DEVS Modeling Formalism: Toward Scientific Foundations for MBSE." *Applied Sciences*, 11(11), 4936.
- Zeigler, B.P., Muzy, A. & Kofman, E. (2018). *Theory of Modeling and Simulation*, 3rd ed. Academic Press.

### Encyclopedia Entries

- "Abstract Systems Theory." *Encyclopedia of Mathematics*. https://encyclopediaofmath.org/wiki/Abstract_Systems_Theory

---

*Document scope: Comparative formal system definitions for BERT grounding and Lean 4 formalization. Does not cover Wymore's T3SD design methodology in full, Klir's reconstructability analysis in full, or Bunge's broader ontological system.*
