# Paper Outline — *Which of Mobus's 12 Principles Are Independent?*
*Working draft outline. Companion figures: `dependency-dag.mmd` (Fig. 1) + the axiom table (Fig. 2).*

**Thesis (one line):** Formalize Mobus's twelve principles and the list becomes a theory — eight independent axioms and four theorems, with a hidden agential layer the prose labels obscured.

**Subtitle option:** *A Machine-Checked Axiomatization of Systems Science.*

## Abstract (draft ~110 words)
George Mobus's *Systems Science* organizes the field around twelve principles, stated in prose and labeled informally as axioms or "corollaries." We give the first machine-checked formalization of all twelve in Lean 4 and ask which are independent. Reconstructing each principle at its tractable core, we find **eight independent axioms and four theorems**: structural complexity derives from systemness, hierarchy, and networks; internal models, self-models, and the genus of information are derived; and — correcting two of Mobus's "corollary" labels — **understandability and improvability are independent axioms about what an *agent* does with a system**, not consequences of modeling and evolution. The twelve thus split into **ten ontological + two agential**, with a **blind/directed axis** separating evolution from engineering. We present the dependency DAG as a candidate axiomatization, with a worked example per finding.

## Section spine

**1. Introduction.** The gap: Mobus states 12 principles as prose with informal "axiom/corollary" labels; no formal account exists of *which depend on which*. The question: independence. The move: formalize each at its core, machine-check, and read off the dependency structure. Contributions (4 bullets): (i) first Lean formalization of all 12; (ii) reclassification — 8 axioms / 4 theorems; (iii) the agential-layer finding (10 ontological + 2 agential); (iv) the dependency DAG as a candidate axiomatization.

**2. Method (brief).** Tractable-core formalization: find each principle's irreducible core, machine-check it in Lean 4 + Mathlib, observe what derives. *Honest scope up front:* cores, not full richness — deferrals named (measure theory in #4/#7, populations/stochastics in #6, Lawvere in #10). Note the de-risking: for "overloaded" principles (#6), the author's own most-formal passage (M&K §10.2.2, "evolution as an algorithm") supplied the spec. Lean → appendix, not body.

**3. The axiom table (Fig. 2).** Walk the 12, one line each (the table from the companion doc). State the headline count: 8 axioms, 4 theorems.

**4. Finding 1 — The reduction (#5 is a theorem).** Every structural complexity measure is a function of #1+#2+#3; the import list is the proof. *Example:* component-kind diversity (the `SameKind` equivalence classes) is computed from the act-on relation alone — no new "typing" primitive. 12 → ≤11.

**5. Finding 2 — The agential layer (the centerpiece).** #11 and #12 are *not* corollaries of #9 and #6. Understanding = a model strictly *simpler* than the system (observe/GET); improvement = an agent with a model + an external goal intervening from outside (intervene/PUT). Independence shown by witnesses (identity model satisfies #9 but not #11; same dynamics admit improvements toward different goals). The 12 split into **10 ontological (what systems ARE/DO) + 2 agential (what an agent does WITH a system)**. *Example:* the **homeostat** — its sensor is the observe/get channel, its set-point-directed correction is the intervene/put channel; one structure (`Homeostat.toLens` + `Homeostat.toImprovement`) carries both. The agent's bidirectional lens onto a system.

**5½. Corollary — the agential principles are orthogonal to complexity (refining Mobus's "6–12 = CAS").** Mobus groups 6–12 as the complex-adaptive-systems principles. The formalization relocates the line: the genuine complex-adaptive threshold is the *model-bearing* line at **#9** — #6 (blind selection) and #8 (set-point) need far less — and **#11/#12 are not complexity principles at all**. They track whether *an agent holds a model* and whether *the system admits a compression*, not how complex the system is. *Two witnesses:* `noisyPairUnderstanding` — a trivial `Bool × Bool` system that is both understandable and improvable; the **prime-cycle** — dynamically richer, yet neither understandable nor improvable, while still evolvable. "Applies to CAS" conflates the system being complex with an agent-with-a-model being present. *(A logical relocation; Mobus's applied point — these get exercised in real CAS — stands. Companion finding #19.)*

**6. Finding 3 — The blind/directed axis (#6 vs #12).** Evolution and engineering both reshape a system, sharing one ontogenic skeleton (variation → selection), but evolution's criterion is *environmental* ("not resident in some mind," M&K), engineering's goal is *mental*. Both independent. *Example:* the **prime-cycle** (3 states, dynamics x↦x+1) — it has a model but no compressing understanding, so no directed agent can improve it, yet it is *evolvable* (a fitness order + a climbing step exist). **Evolvable, not engineerable.** *(Present modestly — see §9.)*

**7. The K ≅ 2 thread.** Modeling (#9), governing (#8), understanding (#11) are the same walking arrow `R → T`: a good regulator contains a model contains the morphism understanding refines. Connect to the convergence thesis (the common core of seven traditions). Short.

**8. The dependency DAG (Fig. 1).** Read the structure off the diagram: 8 axiom nodes, 4 theorem nodes; solid arrows = derives-from, dashed = presupposes; the agential layer and the blind/directed axis as overlays. This is the artifact that turns the list into a theory.

**9. Limits & honest framing.** (a) Cores, not the full principles — the deferrals. (b) The "Mobus got the arrow backwards" claims are *consequences of the chosen cores*, not deductive refutations of Mobus's intent — what rescues them from arbitrariness is **convergence**: the independent formal line matched Mobus 2022's own three-loop ontology (blind auto/biological vs intentional-organization). Lead with the convergence as evidence. (c) #6 is the modest finding — `Evolvable` is a thin predicate, its witness uses a stand-in fitness order; either deepen it (a real fitness landscape) or present lightly.

**10. Conclusion.** The 12 principles as a *checkable* theory; the DAG as a living axiom set that future work (the open stretches: faithful self-model via Lawvere, #7's semantic layer, #6's stochastic tier) extends rather than overturns.

## Figures
- **Fig. 1** — the dependency DAG (from `dependency-dag.mmd`; tidy layout live in Canvas/Chrome, then export — the static SVG floats edge labels).
- **Fig. 2** — the 8-axiom / 4-theorem one-line table.

## Venue / length / trajectory
- **Systems-science framing**, not formal-methods: theory *evidenced by* formalization. Targets: ISSS, *Systems Research and Behavioral Science*, or a sharp **essay/preprint first** (Substack → arXiv) to plant the flag fast, then expand.
- ~6–10 pp for the venue; ~2,000–2,500 words for the essay version.
- **PhD trajectory:** this is the AI-assisted-formalization material Cliff endorsed — a candidate thesis chapter, not only a standalone.

## Gut-check verdict (decide before drafting prose)
**It's a real paper — specifically a short one, anchored on Finding 2.** The agential-layer result is genuinely novel, the convergence with Mobus's own ontology is compelling evidence, and the DAG + axiom table are clean, citable artifacts. Findings 1 and 3 are supporting, not load-bearing (#1 is a tidy reduction; #3 is the modest one). **Recommendation:** publish the **essay/preprint first** (fast flag-plant, lower bar, builds the voice), then expand to the venue paper / thesis chapter. Do *not* aim it at a pure formal-methods audience — the core depth isn't there and isn't the point. If the agential-layer section can't carry ~1,500 words on its own, it's an internal reference, not a paper — but on current evidence, it can.
