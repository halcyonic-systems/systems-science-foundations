# The Common Core Theorem

> A system is a morphism $f: R \to T$ in a category $\mathcal{C}$ — an object of the arrow category $\mathcal{C}^{\mathbf{2}}$.

*Independent definitions of "system," one shared structure.*

> **Revised 2026-07-25.** The existence half is unchanged and is now fully machine-checked, faithfulness included. The **maximality half was wrong twice over** and has been rewritten. The old definition of the common core ("largest connected category admitting a faithful functor into every I_X") is false, and the old proof in this document was invalid on its own terms. Both are replaced below. The corrected claim lives on the dependency quivers rather than on the free categories over them, and is formalized in `Systems/Category/SharedPrimitive.lean`. The diagrams, the embedding table, and the interpretive sections are unaffected.

> **Cold verification (added 2026-08-11).** Every headline claim in this document — the eight embeddings, the repaired quiver-level maximality, and the refutation of the free-category form — is restated with full types in the trusted statement file [`Systems/Challenge.lean`](../../Systems/Challenge.lean). Run `scripts/check-challenge.sh` to verify all 20 statements against the library proofs (kernel-checked, standard axioms only; `connected_is_single_arrow` is axiom-free). A skeptical reader needs that one file plus the quiver definitions it names, not this prose and not the proofs.

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

**Definition.** For each tradition X, let Q_X be its dependency quiver, and I_X := Free(Q_X) the shape category over it.

**Theorem (Existence).** There is a functor **2** → I_X for every X, injective on objects and faithful. Each sends the single arrow of **2** to a *generating arrow* of Q_X, never to a composite.

**Theorem (Shared primitive).** Let Q be a connected quiver admitting, for every X, a prefunctor Q → Q_X that is injective on vertices, sends edges to edges, and is injective on each edge set. Then Q has two vertices and one edge. Its free category is **2**.

The second statement is what replaces "maximality," and the wording matters. The claim is not that **2** is the largest category embedding somewhere. It is that **the only dependency every tradition directly asserts is one.** See *Proof* below for why the free-category version is false and what the quiver level buys.

The common core K ≅ **2**, the walking arrow category:

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

**(1) Existence.** Eight functors constructed via `Paths.lift` from prefunctors mapping the single Klir arrow to a generating arrow in each target. Object-injectivity: `klirTo*_obj_injective`. Faithfulness: every hom-set of **2** is a subsingleton (`klir_path_subsingleton`), so every functor out of it is faithful (`faithful_of_subsingleton_hom`, giving `klirTo*_faithful`). Note this is a property of the *source*: the proof is cheap and says nothing about the targets. ∎

**(2) Why the old maximality proof failed.** The previous version of this document argued that a faithful functor from a connected category into **2** cannot collapse two objects joined by a non-identity morphism, because the morphism and the source identity would both land on `id`. That argument is invalid. In the domain, `f ∈ Hom(x, y)` and `id_x ∈ Hom(x, x)` lie in *different* hom-sets, and faithfulness is injectivity within each hom-set, not across them. Concretely, the three-object chain `a → b → c` is thin and connected and maps faithfully into **2** by collapsing two objects. Faithfulness constrains hom-sets, not objects, so it cannot carry the word "largest."

**(3) Why strengthening the notion is not enough.** Requiring the functor to be faithful *and injective on objects* removes that counterexample and leaves a worse one. Let **V** be the fork: one source, two arrows, two distinct sinks. **V** is connected, has three objects, and embeds into all eight shape categories injectively-on-objects and faithfully. Machine-checked as `SharedPrimitive.free_category_maximality_fails`.

Seven of the eight admit **V** through generating arrows, since each has a vertex of out-degree two. **Joslyn is the leak.** No vertex of Q_Joslyn has out-degree two, but I_Joslyn is a *free category*, so the composite `controller → effector → controlled` is a morphism. **V** enters through a dependency the tradition never asserts. The feedback cycle noted in the table above as "infinite hom-sets" is exactly what creates the extra room.

**(4) The shared-primitive theorem.** Compare the quivers Q_X instead of the categories I_X. Derived composites stop counting, and two traditions then force the result:

- **Q_Joslyn** has no vertex of out-degree two. This kills the fork `x → y`, `x → z` (`no_fork`).
- **Q_Willems** has no vertex of in-degree two, killing the cofork `x → z ← y` (`no_cofork`); no composable pair of edges, killing the two-chain, every self-loop, and every antiparallel pair (`no_two_chain`, `no_loop`); and no parallel edges (`no_parallel`).

Hence in any such Q, two edges either coincide or share no vertex at all (`edges_coincide_or_disjoint`). A connected Q with an edge therefore has exactly one, on two vertices. ∎

The remaining six traditions are **not needed**. The core is forced jointly by the cybernetic shape and the behavioural shape.

**Limits, stated rather than buried.** Quiver-level claims are not invariant under adding derived arrows, unlike free-category ones, so this theorem is relative to the presentations in the diagram above. Drawing Q_Joslyn with an extra `controller → controlled` edge, which one could argue for, readmits **V** and the theorem fails. The defence is that every edge is a documented primitive commitment of its source text; see `docs/language/terminology-concordance.md` in the bert-lenses repo (not this one) for per-cell citations. This is a claim about what the literature asserts, so sensitivity to how each tradition states itself is the subject matter and not a defect. The step from `edges_coincide_or_disjoint` to "a connected quiver has exactly two vertices and one edge" is formalized: `connected_is_single_arrow` (SharedPrimitive.lean), over an arbitrary vertex type with connectivity given by `Zigzag`.

**On the level shift.** `Paths` is left adjoint to the forgetful functor **Cat** → **Quiv**, so the two levels are formally related and the choice is which side of the adjunction carries the comparison. The quiver side is where a tradition's *asserted* primitives live; the category side is where their *consequences* live. Existence was always a quiver-level fact and had merely been stated more weakly than it was proven.

---

*Machine-verified in Lean 4 with Mathlib. Eight shape categories, eight embeddings, zero sorry, zero custom axioms.*

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

**Embedding.** `klirToSpivak` (CommonCore): 0 ↦ parameter, 1 ↦ output, f ↦ expose — the identical pattern to the Myers row. Faithfulness is inherited from I_Klir's shape as for all entries; `klirToSpivak_obj_injective` depends only on `propext`.

*Correction 2026-07-25:* this section originally read "Maximality is untouched (it is target-independent)." That was wrong on both counts. Maximality as then stated was false, and the repaired shared-primitive theorem is emphatically target-*dependent* — it is forced by Q_Joslyn and Q_Willems specifically. Adding an entry can therefore weaken it, if the new quiver is permissive enough to readmit a competitor. Q_Spivak is permissive (out-degree two at `parameter`), so it neither strengthens nor breaks the result; it simply does no work. Future entries must be checked against the fork, cofork, and two-chain obstructions rather than assumed neutral.

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

**Status upgrade 2026-07-25 — Willems is load-bearing.** This addendum introduced Willems as a stress test with "layered status," explicitly not counted in the headline. That framing understates it. In the repaired shared-primitive theorem, Q_Willems supplies three of the four obstructions: no in-degree two, no composable pair, no parallel edges. Q_Joslyn supplies the fourth. **Those two quivers alone force the core, and the other six are unnecessary.** The tradition admitted as the hardest audience for the kernel turns out to be half the reason the kernel is the size it is.

This does not change the counting decision. Willems still collapses onto Mesarović's span at the shape layer, so a ninth-tradition claim would still assert independence on the measure where it provably collapses, and the headline stays eight. But "kernel-neutrality witness" is no longer an adequate description of what it does here.

---

*Sources: Klir (2001), Bunge (1979), Mobus (2022), Myers (2023), Wymore via Wach et al. (2021), Mesarović & Takahara (1975), Joslyn (1995), Spivak (2026).*

---

## Addendum: Bertalanffy — the core is a tradition's whole quiver (2026-08-05)

Bertalanffy (1968), *General System Theory*, ch. 3, p. 55, defines a system verbally:

> "A system can be defined as a complex of interacting elements. Interaction means that elements, p, stand in relations, R, so that the behavior of an element p in R is different from its behavior in another relation, R'."

**Shape.** `I_Bertalanffy` (`ShapeBertalanffy.lean`): 2 objects (`elements`, `interrelation`), 1 generating arrow `interrelation_on_elements : interrelation → elements`. This **is** Q_Klir under renaming — proved, not observed: `positionEquiv` (a bijection of position types), `obj_roundtrip` and `obj_roundtrip'` (mutually inverse object maps, both directions), `arrow_unique`. `bertalanffyToKlir_obj_injective` and its converse depend only on `propext`; the roundtrips and `arrow_unique` are axiom-free.

**The headline stays eight.** By the Willems precedent — a tradition that collapses onto another at the shape layer is not counted as an independent entry — Bertalanffy collapses onto Klir and is recorded as a **convergence witness**, not a ninth tradition. Claiming otherwise would assert independence on precisely the measure where it provably collapses.

**What the collapse is worth, and it is not nothing.** Every other entry embeds Klir's shape *into* something larger; the core has so far been a common part abstracted from richer structures. Bertalanffy is the first tradition whose **entire quiver is the core** — the shared primitive turns out to be a position an actual tradition occupies, reached from organismic biology in 1968, independently of the information-theoretic lineage Klir wrote from in 1969/2001. That is the strongest available answer to the objection that **2** is an artifact of how the encodings were drawn.

**Obstruction audit** (required since the 2026-07-25 Spivak correction; the repaired shared-primitive theorem is target-dependent, so a new entry can weaken it). Q_Bertalanffy is the most restrictive quiver possible and admits nothing Q_Klir does not: `bertalanffy_out_degree_le_one` (no fork), `bertalanffy_in_degree_le_one` (no cofork), `bertalanffy_no_composable` (no two-chain), `bertalanffy_no_parallel`. All four axiom-free. The result is untouched.

**The negative result is the more valuable half.** Bertalanffy's interaction clause carries a condition Klir's `S = (T, R)` does not — the behaviour of an element **must differ** across relations — and that is a predicate on which R qualify, not a position and not a dependency. The quiver cannot express it and the embedding discards it. So **two definitions with isomorphic shapes make different demands**: the shape functor is not injective on definitional content. This is a limit of the method, exhibited with a separating instance rather than asserted, and it bounds what **K ≅ 2** claims — the dependency skeleton is shared; the qualifying conditions that separate a permissive tradition from a demanding one are not visible at this layer.

Bunge makes the near-identical demand — "unlike a mere relation, a connection makes some difference to its relata" (1979, ch. 1 §1.2) — and *does* promote it to definitional force via the nonempty-bondage requirement, which `ShapeBunge` likewise cannot see. Two traditions converging on difference-making, in a register the shape layer discards, is a finding for the mapping layer rather than the category layer.

**The 1972 restatement, now encoded (same day).** Bertalanffy (1972), AMJ 15(4) p. 417 — human-verified against the page — reads "a set of elements standing in interrelation among themselves **and with the environment**." `Bertalanffy72Shape`: 3 objects, 2 arrows (`interrelation_on_elements`, `interrelation_on_environment`), the span `• ← • → •`. The revision is a functor, `bert68To72Pre`, injective on objects, with `environment_is_new` proving no 1968 position reaches the added vertex — so **the definition revising itself is a theorem, not a remark**. This is the pattern the Mobus 7-tuple → 8-tuple pair will follow.

Two honest notes on it. The 1972 span is structurally the same as `MesarovicShape` (Def 1.4) and semantically unrelated — projections of a response function there, two clauses of one English sentence here; another instance of shape identity without semantic identity. And unlike the 1968 quiver, **Q_Bertalanffy72 is permissive**: `bertalanffy72_has_fork` exhibits out-degree two at `interrelation`. By the reasoning recorded for Q_Spivak it neither strengthens nor breaks the shared-primitive repair — it does no work there — but it is stated and proved rather than assumed. Cofork, two-chain and parallel-edge obstructions all hold, axiom-free.

**Standard met.** Shape file, obstruction audit, `lake build` green (2266 jobs), zero sorry, zero custom axioms. **No `CommonCore` embedding row** — an isomorphism is not an embedding into a larger shape, and adding it to the eight-row table would misrepresent the collapse as an expansion.
