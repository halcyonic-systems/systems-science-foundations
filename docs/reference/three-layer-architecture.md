# The Three-Layer Categorical Architecture of Systems

*How K ≅ **2**, systems ontology, and domain-specific categories relate.*

---

## The Insight

Systems science operates at three categorical levels. Prior work has addressed individual levels but never connected all three. This document maps the architecture.

```
┌─────────────────────────────────────────────────────────┐
│                                                         │
│   Layer 0:  K ≅ 2  (the walking arrow)                  │
│                                                         │
│             • ──→ •                                     │
│             R      T                                    │
│                                                         │
│   "A system is a morphism f: R → T"                     │
│   The common core across seven traditions.              │
│   Proved in Lean 4.                                     │
│                                                         │
├─────────────────────────────────────────────────────────┤
│                          ↑                              │
│                     embeds into                         │
│                          ↑                              │
├─────────────────────────────────────────────────────────┤
│                                                         │
│   Layer 1:  Systems Ontology                            │
│                                                         │
│   ┌───┐   ┌───┐   ┌───┐                                │
│   │ N ├──→│   │←──┤ B │    Objects: Component (C),      │
│   └───┘   │   │   └─┬─┘    Boundary (B), Flow-in (N),  │
│   ┌───┐   │ C │     │      Flow-out (G), Environment   │
│   │ E ├──→│   │←────┘      (E), Transform (T),         │
│   └───┘   └─┬─┘            History (H), Timestep (Δt)  │
│   ┌───┐     │                                           │
│   │ G ├───→─┘              Mobus shape: 8 obj, 5 arrows │
│   └───┘                   Bunge shape:  3 obj, 3 arrows │
│                            Klir shape:  2 obj, 1 arrow  │
│                            ... etc. for 7 traditions     │
│                                                         │
│   Domain-independent. Every system has these.           │
│   BERT encodes this layer.                              │
│                                                         │
├─────────────────────────────────────────────────────────┤
│                          ↑                              │
│                   instantiated by                       │
│                          ↑                              │
├─────────────────────────────────────────────────────────┤
│                                                         │
│   Layer 2:  Domain Categories                           │
│                                                         │
│   ┌──────────────┐  ┌──────────────┐  ┌──────────────┐ │
│   │  Gov          │  │  Chain       │  │  Commerce    │ │
│   │               │  │              │  │              │ │
│   │  Objects:     │  │  Objects:    │  │  Objects:    │ │
│   │   Office      │  │   Protocol   │  │   State      │ │
│   │   Body        │  │   Account    │  │   Industry   │ │
│   │   Jurisdiction│  │   Contract   │  │   Commodity  │ │
│   │               │  │              │  │              │ │
│   │  Morphisms:   │  │  Morphisms:  │  │  Morphisms:  │ │
│   │   Appointment │  │   Transaction│  │   Trade flow │ │
│   │   Authority   │  │   State txn  │  │   Supply     │ │
│   │   Oversight   │  │   Delegation │  │   chain      │ │
│   └──────────────┘  └──────────────┘  └──────────────┘ │
│                                                         │
│   + Ecology, Music, Cognition, ...                      │
│                                                         │
│   Domain-specific. Each instantiates Layer 1.           │
│   gov-graphs, blockchain-isomorphism, thesis            │
│   encode this layer.                                    │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

## The Functors

The layers connect via structure-preserving maps:

**Layer 2 → Layer 1 (Interpretation functors):** Each domain category maps down to the systems ontology. These functors say "here's how my domain instantiates the general pattern":

```
F_Gov : Gov → SysOntology          F_Chain : Chain → SysOntology
  Office     ↦  Component             Protocol   ↦  Component
  Appointment ↦  Flow (authority)      Transaction ↦  Flow (value)
  Jurisdiction ↦  Boundary             Network     ↦  Environment
```

**Layer 1 → Layer 0 (Faithful embeddings):** Each tradition's shape category embeds into the walking arrow via the comparison functors proved in Lean 4. The common core K ≅ **2** is the image of these embeddings.

## Positioning Against Prior Work

| | Layer 0 | Layer 1 | Layer 2 | Connection |
|---|---------|---------|---------|------------|
| **Goguen (1978)** | — | — | R-obj, Fin-obj, Ph-obj | No ontology, no common core |
| **Rosen (1958)** | — | M,R-systems | Biology only | No general ontology |
| **Ehresmann (2007)** | — | Colimit-based emergence | Bio, cognitive | No common core theorem |
| **Spivak (2014+)** | — | Operads, wiring diagrams | Engineering, CS | No systems ontology |
| **Mobus (2022)** | — | SL (informal) | Various | No categorical formalization |
| **This work** | K ≅ **2** | Shape categories (Lean 4) | Gov, Chain, Commerce, ... | All three layers connected |

**Goguen** had Layer 2 categories (R-objects, Fin-objects) but no Layer 1 ontology and no Layer 0 common core. He proved systems compose and behavior distributes, but couldn't say what a system *is*.

**Rosen** had a Layer 2 category (metabolic-repair) with implicit Layer 1 commitments, but no generalization beyond biology.

**Spivak/CyberCat** have sophisticated Layer 1 machinery (operads, polynomial functors) but come from math/CS with no connection to the classical systems ontology (Mobus/Bunge/Klir).

**This work** connects all three layers: K ≅ **2** establishes the universal core, the shape categories formalize the ontology, and domain categories instantiate it in specific worlds. The interpretation functors (Layer 2 → Layer 1) are where the real-world applications live.

## Philosophical Grounding

**Mac Lane (1986):** Mathematical structure arises from human activity — listing, counting, comparing, ordering. Table 1.1 maps Activity → Idea → Formulation. The three-layer architecture follows this pattern: human activity in specific domains (Layer 2) gets formalized through systems ontology (Layer 1) and ultimately reduced to minimal structure (Layer 0).

**Mobus (2022):** Systems exist in the world independent of human observers. Humans evolved to recognize systemic structure, not to invent it.

**Synthesis:** Both are right. Systems are real (Mobus). Mathematics is the toolkit humans built to engage with them (Mac Lane). K ≅ **2** is evidence of both — seven traditions independently converged on the same structure because the structure is in the world, and the walking arrow is what the human formal toolkit produces when it tries to capture "thing acting on thing."

Mac Lane also noted (p. 29) that partial orders are underutilized in social phenomena — social scientists collapse rich structure into linear rankings. The Layer 2 domain categories for governance and commerce are partial orders, not linear hierarchies. The categorical framework respects incomparability where it exists.

## Open Pressure Points

*Identified during initial review. These are where scrutiny will land.*

**1. The seven traditions must be fully explicit.** Which seven? Are there traditions that don't embed? Does Beer's VSM embed cleanly, or does recursion (systems within systems) require something beyond the walking arrow?

**2. Interpretation functors (Layer 2 → Layer 1) need to be worked out as actual functors.** Do they preserve composition? If two appointments compose (authority delegation chain), does the image in SysOntology compose correctly as flows? Object-and-morphism lists are not enough — explicit composition rules needed.

**3. Lateral relationships within Layer 1 are underspecified.** What are the functors *between* shape categories? The Mobus → Bunge forgetful functor forgets History and Timestep — what does that mean philosophically? The downward direction (all embed into K ≅ **2**) is handled; the lateral relationships are where the real ontological arguments live.

**4. The Marta Bunge absence belongs in the literature review.** Lawvere-trained topos theorist, married to CESM's architect for 60+ years, same university — zero collaboration. Evidence that the gap is genuine, not merely overlooked.

## References

- Ginali & Goguen, "A Categorical Approach to General Systems," in Klir (ed.) *Applied General Systems Research*, Plenum, 1978, pp. 257–270
- Mac Lane, *Mathematics: Form and Function*, Springer, 1986 (esp. Ch. 1: Origins of Formal Structure, Ch. 11: Sets, Logic, and Categories)
- Mac Lane, *Categories for the Working Mathematician*, Springer, 1971
- Rosen, "The Representation of Biological Systems from the Standpoint of the Theory of Categories," *Bull. Math. Biophys.*, 1958
- Ehresmann & Vanbremeersch, *Memory Evolutive Systems*, Elsevier, 2007
- Spivak, *Category Theory for the Sciences*, MIT Press, 2014
- Mobus, *Systems Science: Theory, Analysis, Modeling, and Design*, Springer, 2022
