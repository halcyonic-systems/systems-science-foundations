# Phase 3 Exploration Log: Polynomial Functors, Operads, and the AlgebraicJulia Bridge
*2026-02-18*

## Status: Exploratory — no Lean formalization, findings only

---

## 3.3 AlgebraicPetri.jl Connection (CONCRETE — verified computationally)

**Script:** `bitcoin-bra/scripts/algebraic_petri_exploration.jl`

### What Worked

BRA Petri nets translate directly to AlgebraicPetri.jl syntax. Three concrete transactions verified:

| Tx | Description | w·pre | w·post | Fee |
|----|-------------|-------|--------|-----|
| Tx1 | split {val 3} → {val 1, val 2} | 3 | 3 | 0 |
| Tx2 | merge {val 1, val 1} → {val 2} | 2 | 2 | 0 |
| Tx3 | fee {val 3} → {val 2} | 3 | 2 | 1 |

All satisfy `w·pre ≥ w·post` (matches `bra_petri_net_invariant` from PetriNet.lean:127).

**Boundedness** verified at all reachable states: `Σ w[p]·m[p] ≤ C` (matches `bra_petri_net_bounded` from PetriNet.lean:136).

**Open Petri net composition** works: Two BRA subnets (System A: merge on {val 1, val 2}; System B: split on {val 2, val 3}) composed along shared species, producing a 3-species 2-transition net. This is the compositional structure the Lean formalization doesn't have.

### Correspondence Table

| Lean (PetriNet.lean) | AlgebraicPetri.jl | Status |
|---|---|---|
| `PetriNet.Place = Fin C` | `nparts(net, :S)` | Direct |
| `PetriNet.Trans = TransitionSpec` | `nparts(net, :T)` | Direct |
| `braWeightVector = p+1` | `w = [1,2,...,C]` | Manual (BRA-specific) |
| `weighted_count_eq_sumValues` | `sum(w .* pre/post)` | Verified |
| `bra_petri_net_invariant` | w·pre ≥ w·post per tx | Verified |
| `bra_petri_net_bounded` | w·m ≤ C at all states | Verified |
| (no equivalent) | Open Petri nets | **NEW** |
| (no equivalent) | Compositional structure | **NEW** |

### Key Insight

The weight vector `w(p) = p+1` is **BRA-specific** — AlgebraicPetri doesn't auto-discover it. It encodes the conservation constraint. General Petri net theory handles arbitrary nets; the conservation structure is domain content that the Lean proof certifies. The tools are complementary: AlgebraicPetri for compositional exploration, Lean for certified properties.

### Next Steps for 3.3

1. Model multi-party BRA transactions as compositions of open Petri nets
2. Could the compositional structure inform `MonoidalCategory BtcState` (the deferred Step 2.4)?
3. Publication-quality Petri net diagrams for the BRA paper

---

## 3.1 Mobus's Boundary as Polynomial Functor (EXPLORATORY — research phase)

### What IS a Polynomial Functor

A polynomial functor `p(y) = Σ_{i ∈ I} y^{B_i}` is an endofunctor on Set where:
- **Positions** (`I`): possible states/modes of the system
- **Directions** (`B_i`): "slots" or "ports" that need filling when in position `i`

A map `p(y)` says: "I am in state `i`, and for each of my `B_i` input slots, I need a value from `y`."

**Morphisms (lenses):** A morphism `p → q` is a forward map on positions + backward map on directions (contravariant). The backward direction is the "adapter" pattern from functional programming.

**Dynamics:** A dynamical system on `p` is a Moore machine: state set `S`, readout `S → I`, update `S × B_{readout(s)} → S`. In Spivak's framework, the polynomial defines the *interface*; the dynamics are maps of polynomials.

### Proposed Mapping: Mobus 8-Tuple → Polynomial

| Mobus Element | Poly Counterpart | Fit | Notes |
|---|---|---|---|
| **B** (boundary/interfaces) | Position set `I` | PARTIAL | Static: clean. Mode-dependent: needs P structure |
| **G** (external flows) | Direction sets `B_i` | GOOD | Fibers of G over interfaces = directions |
| **N** (internal network) | Wiring diagram | GOOD | Capacity `κ` needs enrichment treatment |
| **T** (transforms) | Dynamical system (Moore machine) | STRUCTURAL | Correct type, but T is opaque in Mobus |
| **H** (history) | State set of Moore machine | PARTIAL | H is part of state, not all of it |
| **C** (components) | Sub-polynomial index set | GOOD | Each component is a sub-polynomial |
| **E** (environment) | The argument `y` | CONCEPTUAL | Milieu M has no clean counterpart |
| **Δt** (time scale) | **NO COUNTERPART** | FAILS | Temporal resolution is external to Poly |

### Where It Works Cleanly

**The boundary-interface-flow triangle:**
```
Interface i ∈ I  ←→  position of p_S
G-edges at i     ←→  directions B_i
E.objects        ←→  the "stuff" that fills the directions (argument y)
```

The bipartite constraint (`IsBipartiteFlow` from Interface.lean) maps perfectly: every direction at every position connects to the environment, not to other positions. This IS `BoundaryComplete` — the polynomial's interface is the only way in or out.

**Hierarchical decomposition:** Each component `c_k ∈ C` has its own polynomial; `N` specifies the wiring diagram that assembles them. This maps to Spivak's operadic composition.

**The bridge theorem as forgetful operation:** `toBunge` is a projection from polynomial-typed systems to relation-typed systems. The information loss categories in Bridge.lean enumerate what the polynomial adds beyond the flat relation.

### Where It Breaks Down

1. **Δt has no home.** Polynomial functors are algebraic; temporal resolution is external. This means 7/8 of the tuple maps, with Δt remaining a separate parameter.

2. **Boundary properties P are too vague.** Mobus says P is "still an object of research." The most interesting polynomial feature — mode-dependent interfaces — requires concrete P structure.

3. **Capacity enrichment.** κ on flow edges is quantitative data that pure polynomials don't carry. Needs enrichment (polynomials in a quantitative monoidal category).

4. **Milieu M has no counterpart.** Polynomials model discrete port-based interaction. Ambient non-discrete influence is outside the paradigm.

5. **History is only part of state.** The system state includes current component values + accumulated knowledge; the tuple doesn't cleanly separate these.

### Assessment

**The mapping works for 5-6/8 of the tuple**, and the parts that work are the most structurally important (B, G, N, C, T). The failures (Δt, M) are about features that are specific to Mobus's engineering orientation and have no counterpart in *any* categorical framework — not even Bunge captures them.

**The single strongest value:** Polynomial functors give T (transforms) a precise *type signature*: a lens `state_poly → p_S`. Mobus leaves T as an opaque type parameter. The polynomial framework tells systems scientists what the categorical type of "transform" should be.

### Recommended Next Steps for 3.1

1. **Start with the static polynomial:** Map `(B.interfaces, G-fibers, E.objects)` to a polynomial, ignoring mode-dependence. This is clean and could be verified in CatLab.jl wiring diagrams.
2. **Use CatLab wiring diagrams for N:** Model the internal network as a wiring diagram connecting sub-polynomials.
3. **Document what drops out:** Δt, M, and mode-dependent P are explicitly outside scope.
4. **Save full Poly formalization** for when a Lean polynomial functor library matures or we commit to building one.

---

## 3.2 System Assembly as Operad Algebra (CONCRETE — verified computationally)

**Script:** `systems-ontology/scripts/operad_composition.jl`

### The Claim

Bunge (§1.6): "the set of all systems has no algebraic structure — not even the rather modest one of a semigroup."

The operadic correction: he's right about semigroups, wrong about algebraic structure generally. Systems form an **operad algebra** — composition is possible when boundary conditions match.

### What Worked

Three Bunge-style CES systems modeled as open Petri nets:

| System | Role | Species | Tx | Boundary |
|--------|------|---------|----|----|
| A | Producer | 3 (worker, machine, product) | 1 | output: product |
| B | Consumer | 3 (supply, assembler, warehouse) | 2 | input: supply |
| C | Regulator | 4 (input, sensor, controller, output) | 3 | input + output |

**Sequential composition (Bunge's "merger"):** Producer ∘ Consumer = 5 species, 3 transitions. Producer's output leg glued to Consumer's input leg — shared boundary species identified.

**Three-system chain:** Producer → Regulator → Consumer.
- `(A;C);B` = 8 species, 6 transitions
- `A;(C;B)` = 8 species, 6 transitions
- **Associativity verified** — same species and transition counts for both groupings.

**Parallel + sequential (full operadic toolkit):** Two independent flow systems D, E composed in parallel (disjoint union = 4 species, 2 tx), then fed into a Collector that merges their outputs. Result: 5 species, 3 transitions. This demonstrates both the monoidal product (parallel) and composition (sequential) in a single pipeline.

### Bunge's Vocabulary → Operad Vocabulary

| Bunge | Operad/Category | Correspondence |
|-------|-----------------|----------------|
| boundary | exposed ports / legs | Direct |
| environment | external wiring context | Structural |
| merger | sequential composition (boundary identification) | Verified |
| juxtaposition | parallel composition (monoidal product) | Verified |
| assembly | composition in the operad algebra | Verified |
| "no semigroup" | correct: partial composition | Confirmed |
| "no algebraic structure" | **WRONG**: operad algebra | Demonstrated |

### Why Bunge Was Half-Right

He's right that there is no total binary operation — not every pair of systems can compose. He's wrong that this means no algebraic structure. The partiality IS the structure: composition is defined when boundaries match, and the patterns of boundary-matching form an operad. This is strictly richer than a semigroup.

### Connection to Lean Formalization

| Lean (Systems-Ontology) | CatLab/AlgebraicPetri | Status |
|---|---|---|
| ConcreteSystem ⟨C,E,S⟩ | Open Petri net (species, tx) | Analogy |
| Subsystem σ₁ ≺ σ₂ | Sub-net embedding | Direct |
| Assembly (precursor → result) | oapply (wiring → composite) | Structural |
| NestedSystems | Hierarchical wiring diagrams | Direct |
| (no equivalent) | Operad of composition patterns | **NEW** |
| (no equivalent) | Monoidal product (parallel) | **NEW** |

### Next Steps for 3.2

1. Use CatLab's `UndirectedWiringDiagram` + `oapply` for more complex composition patterns
2. Model Bunge's Fig 1.4 examples (fusion vs. merger) more precisely
3. Verify equivariance (the other operad axiom, beyond associativity)
4. Lean formalization deferred to Phase 4 (depends on operad library maturity)

---

## 3.4 Nester-Lambert Bridge (HIGHLY SPECULATIVE — not attempted)

Not attempted. Requires clear results from 3.1 and 3.2 first. The question: can BRA states with reachability form a site (category with Grothendieck topology) connecting to Lambert's topos-theoretic consensus?

---

## CatLab.jl vs. Polynomial Functors: Different Tools

| Aspect | Wiring Diagrams (Catlab) | Polynomial Functors (Spivak) |
|---|---|---|
| Composition | SMC morphism composition | Lens composition |
| Interface | Fixed input/output ports | Mode-dependent (position/direction) |
| State | External | Internal to dynamical system |
| Feedback | Requires traced monoidal structure | Native via composition product |
| Mode-dependence | No | Yes — THE key advantage |
| Tool support | CatLab.jl (mature) | No Julia/Lean library |

CatLab.jl is the pragmatic tool for now. Full polynomial functor formalization is aspirational.

---

## Key References

- Spivak & Niu, *Polynomial Functors: A Mathematical Theory of Interaction* (2021, arXiv:2312.00990)
- Spivak, *Poly: An abundant categorical setting for mode-dependent dynamics* (2020, arXiv:2005.01894)
- Baez, Libkind, Master, *Structured Cospans* (2022) — AlgebraicPetri's theoretical foundation
- Patterson et al., *Categorical Data Structures for Technical Computing* (2022) — the CatLab.jl paper

---

## Summary: What's Worth Formalizing in Lean?

| Exploration | Result | Worth Lean formalization? |
|---|---|---|
| 3.3 AlgebraicPetri | BRA ↔ Petri net correspondence verified computationally; open net composition works | YES — compositional structure could inform MonoidalCategory BtcState |
| 3.1 Polynomial mapping | 5-6/8 of Mobus tuple maps cleanly; Δt and M don't | MAYBE — static polynomial yes, mode-dependence waits for P |
| 3.2 Operad algebra | Verified: merger, associativity, parallel+sequential pipeline | YES — Bunge systems compose operadically when boundaries match |
| 3.4 Nester-Lambert | Not attempted | NOT YET |
