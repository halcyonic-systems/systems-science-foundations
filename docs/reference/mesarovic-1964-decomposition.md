# Mesarovic 1964 — the decomposition theorem behind Joslyn's Prop 29

**FORMALIZED (cores) 2026-07-11**: `Systems/Mesarovic/Decomposition.lean` — `Set.peel` (part 1's constructive engine, state = prefix history) + `Set.quaternary_two_triadic` (one full crank, 2 = 4−2 factors) + `parityRel`/`binaryJoin` floor theorems. All five declarations **fully axiom-free** (not even propext). Part-2 iff remains the research-level remainder (below).

*First-read note, 2026-07-11 (session ssf-mesarovic-source). Source-acquisition status at bottom. This is the comprehension-first record for the theorem Joslyn cites at p. 14 of Mesarovic 1964, which gates Prop 29's existence direction (deferred in `Systems/Joslyn/Control.lean`).*

## What Joslyn actually says (full passage, Joslyn 1995 pp. 105–106)

Mesarovic "works almost exclusively with the structural kinds of systems … of relations on (subsets of) multidimensional spaces." Decomposition: an n-fold system S is recast as the relational product of an m-fold system T and a p-fold system U, so that **m + p = n and U ∘ T = S**.

> "An important theorem on p. 14 of (Mesarovic, 1964) states that, except for some very special and complex cases, in general a system S can be at most decomposed into (n − 2) 3-fold systems, and not into any collection of 2-fold systems."

Joslyn's use: 2-fold systems admit input/output descriptions; from 3-fold up, one dimension can be neither input nor output — "complex systems require some concept of an internal state." Hence in a control₂ system, O must have internal states that vary to compensate (→ Prop 29's decomposition O = ⟨O_E, O_I⟩).

## THE ACTUAL THEOREM (transcribed 2026-07-11 from scans of pp. 13–17; scans at `~/Desktop/mesarovic/`)

**Setup (p. 13, "Decomposition and State of the System")**: a system is specified explicitly by a polyadic nth-order relation R[X₁, ···, Xₙ] (eq. 15). A relation R is a **relative product** of R₁ and R₂ iff

> (xRy) ↔ [(xR₁z) ∩ (zR₂y)]   (eq. 16)

Decomposition = finding R₁, R₂ with R = R₁/R₂, reticulating S into R₁[X₁, ···, X_j, Z] and R₂[Z, X_{j+1}, ···, Xₙ] (eq. 17). **The connecting middle term Z is a NEW term** — Joslyn's "m + p = n" bookkeeping is his simplification, not the source's.

**Theorem (p. 14, verbatim structure)**: An nth-order system can be:
1. **Decomposed into (n − 2) triadic relations {R₁, ···, Rₙ}** — unconditionally.
2. **Decomposed into dyadic relations if and only if** for every triadic relation obtained from (1):
   - (a) [XᵢRⱼ(Xᵢ₊₁, Xᵢ₊₂)] ↔ {(XᵢRⱼ¹Zⱼ) ∩ [ZⱼRⱼ²(Xᵢ₊₁, Xᵢ₊₂)]}   (eq. 18)
   - (b) **Zⱼ = Xᵢ₊₁ ∪ Xᵢ₊₂**

**The "exception clause" is precise, not vague**: dyadic decomposition is possible exactly when each triadic factor's medium term can be assembled from terms already present (condition b) rather than being genuinely new. "Except for some very special and complex cases" = "unless (18)+(b) hold" — a checkable condition, not hand-waving.

**Proof shape (pp. 14–15)**:
- Part 1 is **constructive**: iterated relative products peel off one coordinate at a time (eqs. 19–22), each step introducing a fresh middle term; "no restriction is imposed when introducing relative products" → n − 2 triadic subsystems, always.
- Part 2 sufficiency: if (18) holds, each triadic factor splits with medium term Yⱼ² (eqs. 24–25) → 2(n − 2) binary subsystems.
- Part 2 necessity: if some triadic factor's medium term cannot be one of the three original terms, any splitting Rⱼ = Rⱼ¹/Rⱼ² introduces a new term Z¹ and Rⱼ² **is again triadic** (eq. 26) — the order never drops. *(Schematic by modern standards: it exhibits the canonical splitting's failure; a formalization must close the "any splitting" generality gap.)*

**Punchline (p. 15, author's emphasis)**: "in general, *a higher order system cannot be decomposed into the subsystems with less than triadic relations*."

**State as a COROLLARY (pp. 15–17)**: the state concept is "introduced as a consequence of the theorem": for X₁RX₂(t) (order p + 1), the relative-product decomposition X₁R₁[X₂ʲ(t), Zʲ] ∩ ZʲR₂X₂ʲʳ(t) (eq. 33) makes "elements of Z represent the state of the system" — embodying the entire past history. p. 17: reducing the order below triadic is impossible "except in the case where the conditions of the theorem are satisfied. **The three terms of the triadic relation are, then, input, output, and state.**"

**Corrections to Joslyn's paraphrase**: (i) part 1 is unconditional, not "at most... except special cases" — the exceptions attach only to the DYADIC question; (ii) the exception clause is the precise medium-term condition (18)+(b); (iii) relative products introduce new terms — his m + p = n arity arithmetic is not the source's convention.

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

## Open questions — RESOLVED 2026-07-11 (source acquired as scans)

1. ~~Relational product~~ → eq. 16: composition through a NEW existentially-connecting middle term; m + p = n was Joslyn's simplification.
2. ~~Exception clauses~~ → precise: (18) + (b) Zⱼ = Xᵢ₊₁ ∪ Xᵢ₊₂ (medium term assembled from existing terms).
3. ~~Proof character~~ → part 1 constructive (iterated relative products); part 2 necessity schematic (canonical-splitting argument with a generality gap to close in formalization).

~~Remaining reconstruction question~~ **RESOLVED (run 8, same day)**: eq. 18+(b) modernized as pivot-factorizability — `MiddleFactorizable R ↔ R = middleJoin R` (`Systems/Mesarovic/Decomposition.lean`), with the factorization quantified over ALL dyadic pairs, closing the necessity proof's "any splitting" gap; parity refuses all three pivots (full n = 3 necessity face). Downstream, Prop 29's existence direction proved **degenerate at the set tier**: trivially true in stable-region form, false in envelope-faithful form (`Control₂.exists_realization` / `toControl₂_envelope_const` in `Systems/Joslyn/Control.lean`) — the faithful version is a dynamical-tier target.

## Verdict (updated 2026-07-11, post-acquisition): /goal run 7 slice now COVERS BOTH DIRECTIONS' CORES

- **Part 1 is now /goal-able**: the unconditional (n − 2)-triadic decomposition is a constructive induction (fresh middle terms as tuple/product types over the remaining coordinates) — no exception clauses involved at all. This is the leg Prop 29's existence direction actually leans on, so **Prop 29 existence is NEARER than assumed**.
- **Parity witness stays /goal-able** as the n = 3 impossibility grounding (binary shadows don't determine ternary relations) — the concrete face of part 2's necessity.
- **Not yet**: the full part-2 iff (18)+(b) — needs the medium-term condition reconstructed in modern typing first, and the necessity proof's "any splitting" gap closed. One dedicated sketch session before any loop.

## Source-acquisition status (2026-07-11) — ACQUIRED

- **1964 chapter ACQUIRED as page scans**: full chapter (pp. 4–24, incl. theorem pp. 13–17, goal-seeking section, references) captured 2026-07-11 from the archive.org lending copy (`viewsongeneralsy0000syst`); screenshots at `~/Desktop/mesarovic/` (11 spreads). TODO: import into Zotero as an item with attachments so the scans have a durable home.
- **DTIC AD0659485** — ACQUIRED (2026-07-11, `~/Desktop/AD0659485.pdf`) and **checked: does NOT contain the p. 14 theorem**. It is Mesarovic's 1967 IEEE SSC conference paper ("General Systems Theory and its Mathematical Foundation"), a foundations restatement: cites the 1964 chapter as ref (1), discusses state objects informally as the auxiliary device for constructive specification, and defers technical content to SRC Report 85-A-66-33 ("On the Auxiliary Functions and Constructive Specification of the General Time Systems") and Windeknecht 1967. Corroborates the state-forcing narrative; useless for the exception clauses. SRC 85-A-66-33 is a further acquisition lead.
- **In library now**: Joslyn 1995 (JXTBBK89, full passage above), M&T 1975 (ZA3E2PD3, full OCR).
