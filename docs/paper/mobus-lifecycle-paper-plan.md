# Mobus life-cycle paper — plan

*Working plan for finishing George Mobus's unfinished paper "Revising and extending the mathematical framework for defining a system" as a co-authorship. Status: pre-draft. Tracking: [bert-lenses#144](https://github.com/halcyonic-systems/bert-lenses/issues/144).*

**Provenance.** This plan is the synthesized winner of a blind model bake-off (2026-07-24, `halcyonic` vault `operations/calibration/blind-pick-ledger.md`): three models answered the identical framing brief blind, ranked without provenance. The spine below is the top-ranked framing (Opus 5); two grafts are harvested from the runners-up (Fable 5, Opus 4.8), noted inline.

---

## 1. Spine — closure under lawful change

The paper's thesis in one sentence: **the 8-tuple must be closed under the transitions that define a life cycle; the paper states the invariant that persists and the class of transitions that preserve it.**

This is the only framing under which the two technical results are *necessary* rather than two unrelated repairs bolted together:

- The typed subset relations (`interfaces_sub`, `disjoint`, `externalFlows_nodes`, `network_components`, `bipartite`) are the **well-formedness predicate** `WF` — you cannot say "the system persists through change" until you can say precisely what stays true.
- Veliov's `ΔS ∈ F(S)` is the **admissibility relation** — what counts as a lawful successor.
- The paper's central theorem is their composition, machine-checked:

  > `S ⊨ WF ∧ S' ∈ F(S) ⟹ S' ⊨ WF`

That single statement is what fills the five empty stage sections.

**Why not the alternative framings.** Leading with the *elegant-accounting win* (the Lean closing the Feb-2025 membership problem) makes the paper a static footnote-cleanup — it cannot organize a life-cycle paper, and makes the paper about a proof rather than about systems changing. Leading with the *defect-and-repair* (∪ monotonicity flaw) is a terrible organizing frame for reader and co-author alike: a paper whose spine is a senior collaborator's error is one he co-authors reluctantly and cites defensively.

**The generous, exact reading of the ∪ problem** *(graft — Fable 5)*: `S_{t+1} = S_t ∪ ⟨ΔS⟩` is not wrong; **union is `F` restricted to one of five stages — the Growth-regime special case.** His own `ΔB = ⟨B \ {b_k}, B ∪ {b_new}⟩` already uses set difference: his notation was ahead of his master equation. The repair *recovers his intent*; it does not overrule it. Say exactly this, in the paper and to him.

---

## 2. Scope — one paper, ruthlessly bounded

### In this paper

| § | Content |
|---|---------|
| §2 | The tuple restated with the typed relations as an explicit `WellFormed` predicate. Interfaces stay named in B *and* are a subset of C — take **neither** Feb-2025 horn, and say why both horns lose something. |
| §3 | `S_{t+1} ∈ F(S_t)` replacing ∪. Half a page on why monotonicity fails, cited to his own `ΔB`. |
| §4 | The closure theorem. The paper's centre. |
| §5 | The five stages, **each characterized as a constraint on `F`**, not as new mathematics: Formation (`F` reaches `WF` from a non-system), Growth, Maturity (`F` admits near-stationary successors), Decline (removal admissible, structure degrading), Dissolution (boundary/interface predicate fails — terminal, `F(S)` has no `WF` successor). **This section is the deliverable.** Mostly writing, not research. |
| App. | The Lean, as warrant. **Not** in the spine. |
| — | A **further-work section** naming the three open problems below — this preempts reviewer demands and makes the cuts honest *(graft — Fable 5)*. |

### Cut, explicitly (named as future work, not faked)

- **The φ/Veliov bridge — cut entirely.** Strongly-convex vs polyhedral constraint sets and the 2nd-order approximation results are about *computing* trajectories; this paper *defines* them. Nobody has defined `F_φ(S)` (the 2026 φ-phase machinery in `bert/docs/lifecycle-dynamics.md`) in Veliov's terms. Genuine follow-up. One sentence of forward reference only.
- **`V_min` / `V_opt` — do not define them.** Do not invent viability thresholds under George's name to plug a hole (this is exactly the overreach that stalls the paper). Make §5's Decline and Dissolution **structural** (component removal, predicate failure) so the paper never needs `V_min`. Then name viability as the open problem — and note that **`F(S)` is precisely the object Aubin-style viability theory takes as input.** The repair hands the hole to a mature literature, which makes George's placeholder look prescient rather than empty. That is the sequel's thesis.
- **History / adaptrode — do not adjudicate.** Keep `H` an opaque carrier and require only that **`F` may depend on `H`** — non-Markovian by construction. This makes room for George's EWMA/adaptrode mechanism without ruling on it, and is the technically correct call anyway, since history-dependence is the whole point of `H`. BERT's Buffering-primitive H decision is an implementation choice and does not belong here.
- **BERT — near-zero presence.** One line in Discussion that an implementation exists. If BERT drives the paper it becomes a tool paper and George becomes a citation inside his own framework.

Discipline rule: this paper contains only results that are **done** (the tuple, machine-checked) or **directly entailed by the chosen formalism** (stages as `F`-regimes). Nothing requiring new proof work goes in. That is what makes it finishable with a senior co-author on his timeline.

**Authorship: George first.** Offered unprompted.

---

## 3. How it is presented to George

**Not the Lean. Not a full draft.** The repo reads as "a machine fixed your paper"; a finished draft reads as *fait accompli* and kills the co-authorship. Send **one artifact: the five empty sections, written** — each a paragraph in his notation — plus a two-page cover memo. You are handing him back the part of his own paper he could not write.

**Cover memo — a two-beat opener:**

1. *(beat 1 — graft, Opus 4.8: relational "you were right")* Open with **his own words from the Milieu exchange** — *"a very elegant and sound manner of accounting for the fact that our 8-tuple will have sets whose members are members of other sets"* — and show `interfaces_sub` as the answer, machine-checked, that **kept his boundary B** (took neither horn of the dissolve-B proposal he sidelined). He posed it; here is the sound accounting.

2. *(beat 2 — Opus 5: the substantive catch)* Then:

   > Your `ΔB` already uses set difference. The master equation was lagging your own notation, not the other way around — so the stages were unreachable for a *formal* reason, not a conceptual one. Here's the closure that catches it up.

   He can check that in five seconds and it is true.

**Then** quote his Knowledge-and-History note back to him — *"the history of the system represents the knowledge of the system's possible states and trajectories, that is probable state transitions"* — and note that this **is** `F(S)`, stated in prose before either of you had the vehicle. Make him the author of the bridge, because he substantially was.

Mention the Lean **once**, at the end, in one sentence: the well-formedness conditions and the closure result are machine-checked; happy to walk through it or leave it in an appendix — his call. **Never ask him to learn Lean.**

**Send it inside two weeks.** A stalled collaboration with a senior researcher decays; do not wait for the gaps to close first — the cuts above exist precisely so you don't have to.

**Contingency.** If he rejects Veliov as the vehicle, do not defend Veliov. The deliverable is *closure*, and the theorem restates over any admissible-successor relation he prefers. Die on closure, not on the citation.

### What NOT to do

- Do not headline the machine-checked proof, or let "Lean" / "Claude" sit in the foreground of authorship. The proof-checker verified; the humans reasoned.
- Do not open the George conversation with the union defect. The defect is the paper's motivation for readers; for George it is wrapped inside his own anticipation of the fix.
- Do not revive the Feb-2025 "dissolve B" proposal — the Lean proved you don't have to.
- Do not attempt `V_min`/`V_opt`, the φ/Veliov bridge, or the adaptrode reconciliation in this paper. Naming them as shared open problems is itself the invitation to keep collaborating.

---

## 4. Open problems handed forward (the sequel hooks)

1. **φ/Veliov bridge** — define `F_φ(S)` in Veliov's strongly-convex/polyhedral terms; connect the 2026 φ-phase machinery to the 2025 2nd-order approximation apparatus. The "dynamics paper."
2. **Viability** — define the viability set characterizing Decline→Dissolution, via Aubin-style viability theory taking `F(S)` as input. `V_min`/`V_opt` get their first real definitions here.
3. **History mechanism** — reconcile George's adaptrode/EWMA multi-timescale consolidation with BERT's Buffering-primitive `H`.

---

## 5. Verified source anchors

- **Lean:** `Tuple.lean` (Apr 30 2026) — `interfaces_sub : boundary.interfaces ⊆ components`, `disjoint`, `externalFlows_nodes`, `network_components`, `bipartite`. Postdates the Feb-2025 blocker doc by 14 months; almost certainly never connected to it.
- **Lean:** `Lifecycle.lean` (Jul 25 2026, SSF #30) — **§4 is now machine-checked.** `wellFormed_of_reaches` is the closure theorem over trajectories of any length; `WellFormed`/`PreTuple` reify §2's conditions as a predicate, with adequacy proved in both directions (`wellFormed_toPre`, `toPre_toMobus`) so the predicate is provably neither stronger nor weaker than the `MobusSystem` type. §3's monotonicity argument is `additive_components_monotone` (no additive regime's trajectory ever loses a component) and the generous reading is `growthStep_additive` (union IS a regime of `F`). `step_not_additive` witnesses non-vacuity. `#print axioms` clean on all of it; cold build passes.
  - **Still to write, not to prove:** §5's five stages as restrictions on `F`. The stage characterizations inherit closure, so this is prose — as the plan intended. Interface removal (needs external-flow retraction as a second edit) and Dissolution as a terminal-state theorem are the two places §5 currently outruns the Lean; say so in the paper rather than proving them here.
- **Veliov citations** (both real and distinct, verified against CrossRef/IIASA):
  - Veliov, V. M. (1989). *Approximations to Differential Inclusions by Discrete Inclusions.* IIASA Working Paper WP-89-017.
  - Veliov, V. (1989). "Second order discrete approximations to strongly convex differential inclusions." *Systems & Control Letters* 13(3), 263–269. DOI 10.1016/0167-6911(89)90073-x.
- **Prior art archive** (vault): the flat Veliov-extract layer lives only in `…/org/research copy/basic/systemness/concepts/`; `gsd_formal_outline.md` (Mar 2025) is the researcher's own companion outline. ⚠️ `H = Hierarchy` contamination in 7 archive files — H is **History**; re-read before reusing any archive synthesis.
- **Existing Mobus corpus** (`bert/docs/`): `lifecycle-dynamics.md`, `mobus-reference.md`, `h-element-theory.md`.
- **Full archaeology** (vault): `operations/sessions/2026-07-23/references/mobus-lifecycle-archaeology.md`.
