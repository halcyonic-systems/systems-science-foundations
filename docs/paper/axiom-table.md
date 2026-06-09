# Mobus's 12 Principles of Systems Science — 8 Axioms + 4 Theorems

*One line each, grouped by verdict. Every entry is machine-checked in Lean 4 (`systems-science-foundations`, zero `sorry`). This is the clean reference list / paper Fig. 2. Full discussion: `../reference/principles-formalization-companion.md`; dependency graph: `dependency-dag.mmd`.*

## Axioms (8 — independent)

**Ontological — hold for any system:**
1. **Systemness** — A system is a bounded, organized collection of systems/primitives; any two systems compose into a supersystem.
2. **Hierarchy** — Organization is hierarchical: within-module interaction exceeds between-module, and lower levels run faster.
3. **Networks** — A system's interior is a directed flow network with capacities.
4. **Dynamics** — A system has a state space and an evolution law; composition multiplies state spaces and combines laws.
8. **Governance** — A governed system has a set-point (reference) not contained in its dynamics; a good regulator contains a homomorphic model of what it regulates (K ≅ **2**).

**Blind change — a near-universal axis:**
6. **Evolution** — A system changes under blind, fitness-non-decreasing environmental selection; needs no model, goal, or understanding.

**Agential — about the observer/designer relation, not the system's complexity:**
11. **Understandability** — To understand a system is to hold a model strictly *simpler* than it (an onto, lossy, non-degenerate compression). *Observe / GET.*
12. **Improvability** — To improve a system is for an agent with a model + an external goal to intervene on its dynamics from outside. *Intervene / PUT.*

## Theorems (4 — derived, not axioms)

5. **Complexity** — Every structural complexity measure is a function of #1 + #2 + #3 (the first reduction: 12 → ≤ 11).
9. **Internal Models** — A one-step-correct internal model is correct at *every* horizon (anticipation is automatic); the model map is exactly the good-regulator homomorphism, so #9 supplies #8.
10. **Self-Models** — A self-model is the diagonal case of #9; existence is trivial (the identity), so the content is faithfulness, not existence.
7. **Information** — Information is a difference that makes a difference (Bateson); Shannon entropy is a bounded special case (entropy ≤ Hartley nonspecificity, equality at the uniform distribution).

## The structure behind the list

- **K ≅ 2 (the walking arrow):** modelling (#9), governing (#8), and understanding (#11) are the same morphism `R → T` — "a good regulator contains a model" is the internal model is the dual of understanding.
- **The agential split:** 10 ontological principles (what systems *are* and *do*) + 2 agential (#11 *observe*, #12 *intervene* — what an *agent* does *with* a system). The agential pair is independent of system complexity.
- **The blind/directed axis:** #6 (environmental, blind selection) vs #12 (mental, directed goal) — one shared ontogenic skeleton, neither reducible to the other. *Seam:* a system can be evolvable yet not improvable (the prime-cycle).
- **Where "complex adaptive" actually begins:** not at #6. The demandingness gradient is ontological core (any system) → regulation (#8) → models (#9, #10) → agency (#11, #12), with #6 a near-universal blind axis. (Companion finding #19.)

### Corrections to Mobus's informal labels
- #11 is **not** a corollary of #9 (it adds a compression axiom #9 lacks).
- #12 is **not** a corollary of #6 (it adds an external goal + a model #6 lacks).
- #5 **is** a theorem, not an axiom (it derives from #1+#2+#3).
