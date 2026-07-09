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

---

## Independent Confirmation: Computable Analysis

The walking arrow **2** appears independently as the fundamental classifying object in computable analysis. Pauly (2015) develops the category of *represented spaces* — sets equipped with a surjection from Cantor space — and shows that the Sierpiński space S = {⊥, ⊤} is the universal classifier for open and closed sets. S is categorically identical to **2**: two objects, one non-identity morphism.

In Pauly's framework, every topological property of a represented space (compactness, overtness, separation, discreteness) is characterized by the computability of a specific map into or out of S. The category of represented spaces is cartesian closed, with S playing the role that **2** plays here: the minimal object that classifies observable properties.

This is convergence from outside systems science entirely. Seven systems traditions independently converge on **2** as the common core of "system." Computable analysis independently converges on **2** as the common core of "observable property." The walking arrow is not an artifact of the systems landscape — it is the categorical structure that emerges whenever a formal tradition needs to distinguish "thing" from "what holds of thing."

*Reference: Pauly, A. (2015). On the topological aspects of the theory of represented spaces. Computability, 5(2), 159–180. arXiv:1204.3763v3.*

---

## Addendum: Eighth Entry — Spivak (2026-07-02)

The body of this document describes the original seven-tradition result as proved. An eighth entry now meets the same shape+embedding standard: Spivak's adaptive arrangements ("Compositional Dynamics in Learning and Mechanics," arXiv:2606.28984, Defs 5.3.1–5.3.2), which define a system as a 0-ary operad morphism carrying (Q, ♯_Q, f⁺, f⁻, U).

**Shape.** `I_Spivak` (`ShapeSpivak.lean`): 4 objects (`parameter`, `output`, `input`, `potential`), 5 generating arrows. `drive : parameter → potential` and `potential_on_parameter : potential → parameter` form a cycle — the second cyclic shape in the landscape. Joslyn's cycle is feedback through *observation* (efferent/afferent); Spivak's is feedback through *value*: the state changes because a potential evaluates it. That cycle is the tradition's new commitment — **potential + reaction: value-driven adaptation** — which no other entry formalizes.

**Embedding.** `klirToSpivak` (CommonCore): 0 ↦ parameter, 1 ↦ output, f ↦ expose — the identical pattern to the Myers row. Faithfulness is inherited from I_Klir's shape as for all entries; `klirToSpivak_obj_injective` depends only on `propext`. Maximality is untouched (it is target-independent).

**The commitments ladder as a theorem.** `myersToSpivak : I_Myers ⥤ I_Spivak` (state ↦ parameter, expose ↦ expose, update ↦ update) machine-checks Remark 4.1.2's ladder claim at the shape level: Spivak = Myers + potential + drive.

**Independence caveat.** Spivak and Myers share the Topos-adjacent community and lens machinery (Myers appears in the paper's acknowledgments). The commitment is new; the sociological independence of this convergence entry is weaker than for the original seven. The `myersToSpivak` inclusion states that relationship in the mathematics rather than hiding it.

**Standard met.** Shape file + CommonCore embedding + table row, `lake build` green, zero sorry.

**Data level (2026-07-06).** `SpivakSystem.lean` carries the entry at ViewGeneration's data-level standard — with a cost of a new kind. The structure is shaped after CLS24 Definition 7 (arXiv:2404.16140: state, reaction, potential, exposure), with the factorization law `step_drives` making "value drives motion" structural: the step must route through the potential via the reaction, and `reaction_const` (constant valuation ⇒ no motion) is the Set-level shadow of the reaction being a bundle map T\*X → TX. The Def 5.3.2 vocabulary is formalized as classifier Props (potential-free, static, stateless, driven), with `potentialFree_static` as the classifier's bite.

Unlike Bunge's bond and Mobus's irreflexivity — *conditions* on (T, R) a kernel may already satisfy — a value channel is *data* the kernel cannot supply. `Kernel.toSpivak` is therefore unconditional, and the cost surfaces as a stratum: every kernel-generated Spivak view is provably potential-free and static (`toSpivak_potentialFree`, `toSpivak_static`) — the kernel is pure exposed structure, all how-it-is, no why-it-moves. Round trip (`toSpivak_toKlir`) and faithfulness (`toSpivak_injective`) match the other views; `toSpivakWith` + `toSpivakWith_driven` prove the converse: supplied value data escapes the stratum while fixing the same kernel. The elaborations thus split into two kinds — conditions vs data — with Spivak the first entry whose cost is provably on the data side.

---

## Addendum: Kernel-Neutrality Stress Test — Willems (2026-07-09)

Willems' behavioral triple Σ = (T, W, B) (1991 Def II.1; 2007 pp. 50–51) entered as a deliberate stress test: the tradition most hostile to I/O orientation, defining a system as nothing but a set of admissible trajectories B ⊆ Wᵀ. If the kernel were secretly an input/output commitment, Willems would refuse it. The verdict is layered, and the layering itself is the result.

**Kernel layer — embeds.** `klirToWillems` (`ShapeWillems.lean`): things ↦ signal, relation ↦ behavior, arrow ↦ evaluate. A behavior is a relation predicated on signal values; `dep_on` is predication, not causation, so the behavioral stance has nothing to refuse. The kernel survives its hardest audience.

**Shape layer — collapses.** As a shape, I_Willems is the span time ← behavior → signal, isomorphic to Mesarović's Shape 2 span (`willemsToMesarovic` + inverse + object bijection + four arrow-correspondence theorems). The iso is forced to send `time ↦ input` and `behavior ↦ globalState` — semantically absurd assignments, since Willems has no state object (state is a latent variable of a *representation*, 1991 Def VII.1) and his time axis is nobody's input. The absurdity demonstrates the collapse is a shape-level artifact: the abstraction discards exactly what Willems means.

**Composition layer — independent, not encoded.** Willems' genuine novelty (interconnection as B₁ ∩ B₂, I/O partition as theorem, latent-variable elimination) lives at the composition layer, which shape categories do not measure. Tracked as SSF #16.

**The refinement this forced: entries are claims-at-a-layer.** The existing eight entries are all shape-layer claims and are unaffected in content — each contributes a distinct single-system dependency shape. Willems is NOT counted as a ninth tradition, and the reasoning is now uniform: a ninth-tradition claim would assert independence on the one measure (single-system shape) where Willems provably collapses. Spivak's precedent does not transfer — his caveat is sociological while his commitment stays shape-visible. Counting Willems would make "N traditions" mean two different things across rows. The headline stays eight; Willems ships as a kernel-neutrality witness with layered status.

**Standard met.** Shape file + kernel embedding + both-direction collapse comparison, `lake build` green, zero sorry.

---

*Sources: Klir (2001), Bunge (1979), Mobus (2022), Myers (2023), Wymore via Wach et al. (2021), Mesarović & Takahara (1975), Joslyn (1995), Spivak (2026).*
