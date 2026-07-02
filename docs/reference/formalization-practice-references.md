# Formalization Practice References: LAMP and Scott 1972

*Two June 2026 arXiv papers that bear directly on how SSF proving work is done. Full analyses in the vault: `operations/sessions/2026-07-01/` (session-four-papers-convergence + references/scott1972-lean-mining.md). This doc carries only what SSF work needs day to day.*

## LAMP — agentic proving for unformalized domains (arXiv:2606.28841)

Santhana Srinivasan R & Patawar, IIITDM Kancheepuram. A general-purpose LLM inside a deterministic Planner/Builder/Verifier orchestration, grounded by an MCP "domain ontology tool" (exact Lean statements + dependencies + related concepts), hits **96.7% pass@1** on 90 theorems in a domain with zero prior Lean coverage (Combinatorics on Words). Specialized fine-tuned provers given the same ontology access score 1–9%. Ablations: removing the ontology tool costs −12.3 points (hard tier: 88% → 47%); collapsing Planner/Builder into one agent costs −11.1 points.

**Why it matters for SSF:** SSF is exactly LAMP's setting — an unformalized domain with a growing bespoke library. The finding is that *inference-time structured knowledge beats fine-tuning* for correctness-critical formal work, and the marginal value concentrates in (a) the grounding tool and (b) enforced loop discipline (bounded budgets; cheap re-ground vs expensive re-plan), not in exotic orchestration.

**Adopted into the lean-formalize skill** (see skill Phase 3): bounded re-plan/re-build budgets and the re-ground/re-plan failure distinction.

**Phased plan (agreed 2026-07-01):**
1. **SSF ontology tool** — ✅ done 2026-07-02: `scripts/ontology.py` (stdlib-only CLI; lookup/search/deps/module/stats text layer + kernel-true `axioms` via `lake env lean`). MCP wrapper only when needed.
2. **Skill discipline** — done (lean-formalize skill).
3. **Autonomous harness** — only if the manual loop with the ontology tool plateaus.

Caveat for any sovereign-stack version: LAMP is strongly backbone-sensitive (96.7% Kimi K2.6 vs 68.9% DeepSeek V4 Pro; scaffolding does not equalize weak backbones). Local Gemma-class models would sit well below these numbers.

## Scott 1972 formalization — engineering patterns (arXiv:2606.30782)

Lars Warren Ericson (Catskills Research Company, solo, no institution): complete sorry-free Lean 4 formalization of Scott's *Continuous Lattices* (1972) — 43 numbered results, D∞ ≅ [D∞ → D∞] capstone, classical footprint `[propext, Classical.choice, Quot.sound]` throughout.

**Genre precedent.** Cite at convergence-thesis C3: an independent external instance of "formalization cost dropped to one person + Claude + a proof assistant." Distinction to keep sharp in positioning prose: Ericson mechanizes *one paper* depth-first; SSF extracts a common core across *seven traditions* plus a convergence theorem — the genre extends to cross-tradition synthesis, which is the harder claim. His §7.1 AI-attribution statement (tools named per-task, explicit no-LLM-coauthor stance citing COPE) is the template for SSF's own journal-submission attribution section.

**Patterns adopted or queued (ranked; full detail in the vault mining note):**

1. **Instance-diamond avoidance** (their "specialization preorder diamond"): never register a second competing `Preorder`/`TopologicalSpace` instance on a type that already carries one via another import chain — keep the competitor as an explicit term (`@IsOpen _ scottTop ...` or tightly-scoped `letI`). *Action: audit `Evolution.lean`'s fitness preorder before adding order/topology structure anywhere.*
2. **Results-catalog table** (paper numbering → Lean identifier → module), one row per formalized result. SSF's axiom table covers the 12 principles; a full per-tradition catalog (Klir/Bunge/Mobus Def/Thm number → identifier) is a scrape-and-tabulate job worth doing before the journal push.
3. **Per-proof "engineering notes" micro-format**: one bolded one-line heuristic + one-paragraph justification, attached to the specific proof that generated it. Adopted into the lean-formalize skill (Phase 4).
4. **Friction as diagnostic**: their Prop 4.1 had to be proved by a different route than Scott's own (order-theoretic adjunction instead of topological injectivity) because mechanization exposed a soundness trap the prose glossed. Same pattern as SSF's Bunge asymmetric→antisymmetric correction — cite the two together in the journal paper as independent "mechanization corrects the source" cases. Adopted into the skill (Phase 3 discipline).
5. **Conjunction splitting**: state `_a`/`_b` lemmas for conjuncts with different proof engines, keep a bundled wrapper for citation fidelity to the source numbering.

**Before citing as precedent:** verify the repo builds — `git clone github.com/catskillsresearch/scott1972 && lake build` — rather than taking the PDF's sorry-free claim on faith.
