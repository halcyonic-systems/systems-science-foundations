# Mesarovic 1964 — the decomposition theorem behind Joslyn's Prop 29

*First-read note, 2026-07-11 (session ssf-mesarovic-source). Source-acquisition status at bottom. This is the comprehension-first record for the theorem Joslyn cites at p. 14 of Mesarovic 1964, which gates Prop 29's existence direction (deferred in `Systems/Joslyn/Control.lean`).*

## What Joslyn actually says (full passage, Joslyn 1995 pp. 105–106)

Mesarovic "works almost exclusively with the structural kinds of systems … of relations on (subsets of) multidimensional spaces." Decomposition: an n-fold system S is recast as the relational product of an m-fold system T and a p-fold system U, so that **m + p = n and U ∘ T = S**.

> "An important theorem on p. 14 of (Mesarovic, 1964) states that, except for some very special and complex cases, in general a system S can be at most decomposed into (n − 2) 3-fold systems, and not into any collection of 2-fold systems."

Joslyn's use: 2-fold systems admit input/output descriptions; from 3-fold up, one dimension can be neither input nor output — "complex systems require some concept of an internal state." Hence in a control₂ system, O must have internal states that vary to compensate (→ Prop 29's decomposition O = ⟨O_E, O_I⟩).

## Modern restatement (target carrier: `JoslynSystem ι X`, landed 2026-07-10)

Over S ⊆ ∏ᵢ Xᵢ:

- **Negative direction (the load-bearing part for Joslyn)**: n-ary relations are, in general, NOT reconstructible from binary structure. This is recognizably **Peirce's reduction thesis** shape (ternary irreducible to binary; ternary sufficient) — worth flagging as prior-art resonance in any writeup.
- **Positive direction**: every n-ary relation decomposes into (n − 2) ternary relations (under composition conventions that need the source text — see open questions).

## Hand-checked 3-dimensional witness (the impossibility core, verified by hand 2026-07-11)

Parity: S = {(x,y,z) ∈ {0,1}³ : z = x ⊕ y} — 4 of 8 triples.

All three binary projections are FULL: π_{xy}(S) = {0,1}² (z := x⊕y always extends), π_{yz}(S) = {0,1}² (x := y⊕z), π_{xz}(S) = {0,1}² (y := x⊕z). So the join/reconstruction from binary traces is the whole cube (8 triples) ≠ S (4 triples). **A genuinely 3-dimensional relation is not determined by its binary shadows.** The third dimension carries information reducible to neither of the other two — the formal seed of "internal state is forced."

This witness needs only `Set`, `Prod`, and `Bool`/`Fin 2` — fully within SSF's set tier, no new machinery.

## Relation to Mesarovic & Takahara 1975 (in library, Zotero ZA3E2PD3, full OCR verified)

The mature theory runs the SAME insight in the positive direction. **M&T Thm 1.1** (Ch. II, p. 12): *every* general system S ⊆ X × Y has a total global-response function R : C × X → Y with (x,y) ∈ S ↔ ∃c, R(c,x) = y — a state object C always EXISTS (proof: C indexes the functional branches {f : f ⊆ S}). Read together:

- 1964 p. 14: you cannot in general do WITHOUT a third (state) coordinate — impossibility.
- 1975 Thm 1.1: a state coordinate always SUFFICES to functionalize the relation — possibility.

The pair is the two-sided justification of state-based systems theory, and the 1975 side is already on disk. Note: M&T's Thm 1.1 proof builds an arbitrary index set over the set of all functions contained in S — expect classicality (choice) in any faithful formalization of the existence direction; the polarity heuristic (companion doc) predicts the NEGATIVE direction (parity witness) is constructive.

## Open questions (need the 1964 text itself)

1. Mesarovic's exact notion of "relational product" (the m + p = n arity arithmetic suggests composition along a shared coordinate that is consumed — confirm).
2. The exception clauses ("except for some very special and complex cases") — which systems DO decompose into 2-fold systems? These hypotheses ARE the formalization difficulty for the positive direction.
3. Whether p. 14's proof is constructive or cardinality/counting-based.

## Verdict: /goal-able slice EXISTS (negative direction only)

**Yes** — and it does not need the 1964 text: formalize the parity witness as `binary projections do not determine ternary relations` at the set tier (`∃ S₁ S₂ : Set (Fin 2 × Fin 2 × Fin 2), S₁ ≠ S₂ ∧ all three binary projections agree` — or the sharper join-reconstruction form). This machine-checks the impossibility core that Joslyn's "internal state is forced" argument rests on, without touching the exception clauses.

**Not /goal-able yet**: the positive (n − 2)-ternary decomposition and hence Prop 29's existence direction — blocked on the source (exception clauses unknown). Do not attempt from the paraphrase.

## Source-acquisition status (2026-07-11)

- **1964 Views on General Systems Theory (Wiley)**: NOT in Zotero. Internet Archive has it (`viewsongeneralsy0000syst`) but lending-restricted — borrowable with a free archive.org account (1-hr loans); djvu text and search-inside both blocked unauthenticated. ResearchGate lists the chapter ([record](https://www.researchgate.net/publication/266693225_Foundations_for_a_general_systems_theory)); Google Books is snippet-only. Best routes: archive.org borrow (read p. 14, transcribe the theorem + exceptions) or ILL scan.
- **DTIC AD0659485** ("General Systems Theory and its Mathematical Foundation", Mesarovic, SRC report): open PDF at apps.dtic.mil, rate-limited at fetch time — likely contains a mature restatement; retry pending.
- **In library now**: Joslyn 1995 (JXTBBK89, full passage above), M&T 1975 (ZA3E2PD3, full OCR).
