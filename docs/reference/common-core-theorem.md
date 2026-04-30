# The Common Core Theorem

> A system is a morphism $f: R \to T$ in a category $\mathcal{C}$ — an object of the arrow category $\mathcal{C}^{\mathbf{2}}$.

*Seven independent definitions of "system," one shared categorical structure.*

---

## The Landscape

Each tradition defines "system" as a tuple with structural dependencies between positions. We encode these as **shape categories** — free categories on dependency quivers — and ask: what structure do they all share?

```
                        ┌─────────────────────────────────────────────┐
                        │         STRUCTURAL / INWARD                 │
                        │     (arrows converge toward components)     │
                        │                                             │
                        │   I_Mobus (8 obj, 5 arrows)                │
                        │   ┌───┐  ┌───┐  ┌───┐                     │
                        │   │ N ├─→│   │←─┤ B │                     │
                        │   └───┘  │   │  └─┬─┘                     │
                        │   ┌───┐  │ C │    │    ┌───┐ ┌───┐ ┌────┐ │
                        │   │ E ├─→│   │←───┘    │ T │ │ H │ │ Δt │ │
                        │   └───┘  └─┬─┘         └───┘ └───┘ └────┘ │
                        │   ┌───┐    │           (isolated vertices)  │
                        │   │ G ├──→─┘                                │
                        │   └───┘                                     │
                        │                                             │
                        │   I_Bunge (3 obj, 3 arrows)                │
                        │        ┌───┐                                │
                        │   ┌────┤ S ├────┐                          │
                        │   ▼    └───┘    ▼                          │
                        │  ┌───┐        ┌───┐                        │
                        │  │ C │←───────┤ E │                        │
                        │  └───┘        └───┘                        │
                        │                                             │
                        └──────────────────┬──────────────────────────┘
                                           │
                                           │
                    ┌──────────────────────┐│┌──────────────────────────┐
                    │                      │││                          │
              ╔═════╪══════════════════════╪╪╪══════════════════════════╪═════╗
              ║     │     COMMON CORE      │▼│                         │     ║
              ║     │                      │                           │     ║
              ║     │            f         │                           │     ║
              ║     │       0 ────→ 1      │                           │     ║
              ║     │                      │                           │     ║
              ║     │       K  ≅  𝟐        │                           │     ║
              ║     │                      │                           │     ║
              ║     │   "relations depend  │                           │     ║
              ║     │    on things"        │                           │     ║
              ║     │                      │                           │     ║
              ╚═════╪══════════════════════╪═══════════════════════════╪═════╝
                    │                      │                           │
                    │                      │                           │
                        ┌──────────────────┴──────────────────────────┐
                        │                                             │
                        │       OPERATIONAL / OUTWARD                 │
                        │    (arrows radiate from state)              │
                        │                                             │
                        │   I_Myers (3 obj, 2 arrows)                │
                        │        ┌───────┐                            │
                        │   ┌────┤ State ├────┐                      │
                        │   ▼    └───────┘    ▼                      │
                        │  ┌─────┐        ┌────┐                     │
                        │  │ Out │        │ In │                     │
                        │  └─────┘        └────┘                     │
                        │                                             │
                        │   I_Wymore (4 obj, 3 arrows)               │
                        │        ┌───────┐                            │
                        │   ┌────┤ State ├────┬────┐                 │
                        │   ▼    └───────┘    ▼    ▼                 │
                        │  ┌─────┐        ┌────┐ ┌───┐              │
                        │  │ Out │        │ In │ │ T │              │
                        │  └─────┘        └────┘ └───┘              │
                        │                                             │
                        │   I_Mesarovic (3 obj, 2 arrows)            │
                        │        ┌───────┐                            │
                        │   ┌────┤   C   ├────┐                     │
                        │   ▼    └───────┘    ▼                      │
                        │  ┌───┐          ┌───┐                      │
                        │  │ V │          │ Y │                      │
                        │  └───┘          └───┘                      │
                        │                                             │
                        └─────────────────────────────────────────────┘

              ┌───────────────────────────────────────────────────────────┐
              │          CYBERNETIC (cyclic — unique in the landscape)    │
              │                                                          │
              │   I_Joslyn (3 obj, 3 arrows, FEEDBACK LOOP)             │
              │                                                          │
              │        ┌────┐    disturbance    ┌─────┐                 │
              │        │  C ├──────────────────→│ Oₑ  │                 │
              │        └────┘                   └──┬──┘                 │
              │                            efferent│  ▲                 │
              │                                    ▼  │afferent         │
              │                                 ┌─────┴─┐               │
              │                                 │  Oᵢ   │               │
              │                                 └───────┘               │
              │                                                          │
              └───────────────────────────────────────────────────────────┘
```

---

## The Theorem

**Definition.** For each tradition X, let I_X := Free(Q_X) be the shape category (free category on the dependency quiver).

**Definition.** The *common core* K is the largest connected category admitting a faithful functor into every I_X.

**Theorem.** K ≅ **2**, the walking arrow category:

```
         f
    0 ───→ 1
```

with Ob(**2**) = {0, 1}, one non-identity morphism f : 0 → 1.

---

## The Embeddings

Each row is a faithful functor E_X : **2** → I_X.

```
    𝟐                Klir         Bunge        Mobus          Myers       Wymore     Mesarović     Joslyn
  ─────           ─────────    ──────────    ────────────    ─────────   ─────────   ──────────   ──────────

    0     ↦       relation     structure'    intNetwork      state       state       globalState  effector

    │ f                │              │             │              │           │             │           │
    ▼                  ▼              ▼             ▼              ▼           ▼             ▼           ▼

    1     ↦       things       composition   components      output      output      output       controlled


  arrow:          rel_on_      struct_on_    network_on_     expose      readout     response_    efferent
                  things       comp          components                              output
```

---

## What It Means

**A system, in the sense shared by all seven traditions, is a morphism.**

A functor F : **2** → **Set** is a function F(f) : R → T from a set of relations to a set of things. The category of all such systems is the arrow category **Set**^→.

Each tradition elaborates this single morphism into a richer diagram:

| Tradition | What it adds beyond **2** | Categorical content of the addition |
|-----------|--------------------------|-------------------------------------|
| **Klir** | nothing | *is* the common core |
| **Bunge** | environment E, second projection S → E | system-environment distinction (ontological boundary) |
| **Mobus** | boundary, flows, transforms, history, timescale | spatial decomposition (N, G, B) + temporal parameters (T, H, Δt) |
| **Myers** | input, update function | dynamics (state transitions from external input) |
| **Wymore** | input, time, update + time-indexing | dynamics + explicit temporal structure |
| **Mesarović** | second projection C → V | bidirectional I/O observation (not just output) |
| **Joslyn** | feedback cycle (efferent/afferent) | cybernetic closure (algebraically distinct — infinite hom-sets) |

---

## The Structural Divide

The embedding table reveals a deep asymmetry in how traditions interpret the common core:

**Structural traditions** (Bunge, Mobus) map **0 ↦ relation-like** and **1 ↦ thing-like**.
The morphism f means: *relations are defined over things*. Direction: inward.

**Operational traditions** (Myers, Wymore, Mesarović) map **0 ↦ state** and **1 ↦ output**.
The morphism f means: *state determines observables*. Direction: outward.

**Cybernetic tradition** (Joslyn) maps **0 ↦ effector** and **1 ↦ controlled**.
The morphism f means: *the regulator constrains what it controls*. Direction: circular (but the embedding picks one arc of the loop).

Same arrow. Three interpretations. The divergence IS the history of systems science.

---

## Proof

**(1) Existence.** Seven faithful functors constructed via `Paths.lift` from prefunctors mapping the single Klir arrow to a generating arrow in each target. Faithfulness: Hom_**2**(0, 1) = {f} is a singleton; injectivity on singletons is trivial. ∎

**(2) Maximality.** |Ob(**2**)| = 2. By pigeonhole, no 3-object connected category embeds object-injectively into **2**. Non-injective faithful embeddings of connected categories into **2** must collapse two objects sharing a non-identity morphism, sending that morphism to a self-loop. But Hom_**2**(i, i) = {id} for both objects, so the non-identity morphism maps to identity — while the domain's identity at the source also maps to identity. Since these are in the same hom-set (after collapse), faithfulness (= injectivity per hom-set) is violated. ∎

---

*Machine-verified in Lean 4 with Mathlib. Seven shape categories, seven embeddings, zero sorry.*

*Sources: Klir (2001), Bunge (1979), Mobus (2022), Myers (2023), Wymore via Wach et al. (2021), Mesarović & Takahara (1975), Joslyn (1995).*
