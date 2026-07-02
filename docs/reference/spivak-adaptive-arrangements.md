# Spivak's Adaptive Arrangements and the K ≅ 2 Kernel

*Source: D.I. Spivak, "Compositional Dynamics in Learning and Mechanics," arXiv:2606.28984 [math.CT], June 2026. Full deep-read analysis: vault `operations/sessions/2026-07-01/references/spivak-arrsm-vs-kernel.md`. This doc is the durable SSF-side reference: what the paper claims, why it matters for the common-core program, and what the candidate entry-#8 formalization target is.*

## What the paper does

One compositional syntax — the operad **Arr_Sm** of *smooth adaptive arrangements* (reactive parameter space + lens + real-valued potential) — with two functorial semantics into the 2-category **ℙC** of polynomial coalgebras. The configuration integrator Φ_conf recovers gradient descent with backprop as the lens backward pass; the phase integrator Φ_phase recovers Hamiltonian-style mechanics. Applied to the *same* arrangement of harmonic particles on a graph, Φ_conf yields the discrete heat equation (dissipative) and Φ_phase the discrete wave equation (conservative), both governed by the graph Laplacian. "Two semantics of one syntactic object" (Remark 7.4.2).

## Definition 5.3.2 unpacked: "a system is a morphism"

Spivak defines (p.39): a multimorphism φ: b₁,...,b_K → c in Arr_Sm is

> "**a system** if its domain is I (i.e. the arity is K = 0); **a closed system** if it is a morphism I → I."

Unpacking, term by term:

**Operads are composition syntax.** A (colored) operad has objects = *interfaces* (box types, here pairs (M⁻, M⁺) of input/output spaces) and morphisms that are many-to-one: φ: b₁,...,b_K → c is "an arrangement of K inner boxes wired inside one outer box c." Composition is nesting — plug arrangements into arrangements. Nothing in the syntax is a "thing"; everything is a way of wiring.

**Arity K counts the inner boxes.** A 2-ary morphism wires two boxes into one. A 0-ary morphism φ: I → c has *no inner boxes* — its domain is the monoidal unit I = the empty tensor product, "nothing." A 0-ary morphism is therefore a way of *filling* the box c outright: a leaf of the composition tree, the atom of the syntax.

**So "a system" = a filled box = an arrow from nothing.** What we would naively call an object — a component, an entity, a thing — is in this syntax an arrow I → c. Its content is the arrangement data (Q, ♯_Q, f⁺, f⁻, U): internal state, reaction, behavior maps, drive. There are no things at the bottom of the ontology; it is arrows all the way down.

**The boundary is the arrow's type.** An open system is I → c with c = (M⁻, M⁺) nontrivial: the codomain *is* the interface — input port and output port. The boundary is not a component of the system; it is the typing of the system-morphism. (Compare Mobus: the boundary as what disciplines flows, not a part among parts.) A **closed system** I → I has trivial interface — no ports — and under Φ its image is a bare function S → S: an autonomous trajectory. Definition 5.3.2's full vocabulary (stateless / potential-free / static / closed / harmonic) is a formal classifier over these arrows.

**Decomposition = factorization.** A composite system wire_K(•,...,•): I → c is literally the operadic composite of its subsystem-arrows with the wiring-arrow. To decompose a system is to exhibit a factorization of its morphism. This is the BERT move — boundary, subsystems, flows — as arrow algebra.

**Why this is K ≅ 2.** The kernel theorem says the irreducible categorical content of "system" across the seven traditions is the walking arrow **2** — to give a system is to give one morphism (relations depending on things). A functor out of **2** into any category picks out exactly one morphism. Spivak's definition is that statement made natively: to give a system is to pick out a morphism; his tradition's elaborations specify *which category the arrow lives in* (RVect-parameterized manifold lenses with potentials). Kernel: "a system is an arrow." Tradition: "in this category." Same division of labor as the Klir/Bunge/Mobus derived views.

**Both faces are kernel-shaped.** The syntax side: system = morphism I → c in Arr_Sm. The semantics side: its dynamics = a polynomial coalgebra f: S → p(S) — again one morphism, dynamics conditioned on state, whose readout/update unpacking is exactly Myers' expose/update lens. The dynamics functor Φ maps kernel-instance to kernel-instance.

## The candidate entry #8

Remark 4.1.2 presents the framework as an explicit commitments ladder (each stage adds exactly one commitment over the last — the P3 move as categorical structure):

| Stage | Adds |
|---|---|
| Lens_Fin^op (prisms) | static typed routing — things + connections (Klir-root level) |
| Lens_M | ambient spaces (arbitrary smooth maps, not just projections) |
| Lens_M^R | **potential** threaded through the backward pass — drive/value |
| Arr_D = ℙara_Q(Lens_M^R) | **reactive parameter** Q — adaptive state |

Proposed convergence-table row: **Spivak 2026 | Adds: potential + reaction (♯) | Captures: value-driven adaptation — learning and mechanics as one commitment.** No existing tradition in the table formalizes *why* state moves (drive/teleonomy); Spivak makes the potential "the datum at the center."

Caveats to state wherever the row is claimed:
1. **Independence is weaker than for the original seven.** Spivak and Myers share a community and machinery (Poly, lenses; Myers is in the acknowledgments). The commitment is new; the sociological convergence evidence is weaker than Klir-vs-Mobus.
2. **The machine-checked bar.** The other entries are backed by Lean view-generation with round trips. Entry #8 at that standard = formalize the adaptive-arrangement datum D = (𝓜, 𝓠, J, R) (Def 4.1.1 — four pieces of structure: cartesian 𝓜, symmetric monoidal 𝓠, strong monoidal J, monoidal monad R) and derive "system = 0-ary morphism" as a kernel view with named preconditions. Real proof work; tractable scope.

## The two-integrators result and P2b

Φ_conf and Φ_phase share the entire polynomial interpretation Φ'_sm and differ only in the integrator — the choice of stored state (S := Q vs S := T*Q). They are *not* two faithful views of one behavior: the integrator adds ontology, and the same arrangement yields heat vs wave. This is **P2b in dynamical form** — the core generates the traditions: one syntactic object generates the gradient-descent tradition and the Hamiltonian tradition as two commitment-labeled completions. It is also the categorical pattern for the compose/BERT "two faces of the 8-tuple" claim: *face = functorial semantics out of the syntax operad; integrator choice = the named commitment.*

## Secondary hooks

- **Example 4.3.8 (syntactic datum):** spaces can be an algebraic syntax rather than manifolds; a neural network is "a finite syntactic term, not an arbitrary smooth map," with semantics by functor — the deterministic-generator pattern (model as typed term, compiled semantics) inside applied CT.
- **Remark 7.3.2:** vertex = pure mass, edge = stateless bond; "each bond is like a 'training loss' provided to each mass by its neighbor"; squared-error loss *is* a harmonic bond. Direct resonance with the Bunge bond-locus (endo/exo) reading of structure.
- **Remark 7.4.3:** a learner wired to observe any closed system trains a predictor of its one-step map — the world-models claim in one remark.
- **Prop 6.6.1:** for harmonic arrangements the phase step is kick ∘ drift and exactly preserves the symplectic pairing — the conservative face is machine-checkable.
- **Sequel to watch:** conclusion announces a "linear stratum" suboperad with second-order Taylor retraction about critical points — linearization-as-approximation-functor, adjacent to the multi-timescale/fixed-point program.
- **Companion code:** github.com/dspivak/dap — "written entirely by Claude from the definitions in Sections 5 and 6" (fn. 23), reproducing all four worked examples.
- **Predecessor:** Capucci–Lynch–Spivak, *Organizing Physics with Open Energy-Driven Systems*, arXiv:2404.16140 (continuous-time; the overlap category ℛ of Prop 6.5.1 is the shared substrate). Read before attempting the entry-#8 formalization.

## Formalization targets (in order)

1. Encode the 0-ary-morphism definition of system and the open/closed classifier (Def 5.3.2 vocabulary) over a minimal operad structure; show the kernel functor **2** → (system-arrows) — the "system = morphism" verification.
2. Encode the abstract adaptive-arrangement datum (Def 4.1.1) and the commitments ladder (Remark 4.1.2) as named preconditions over the kernel — the entry-#8 gate.
3. (Stretch) The two-integrators split as two views generated from one object — P2b dynamical form, likely needs substantial Poly infrastructure; assess mathlib coverage first.
