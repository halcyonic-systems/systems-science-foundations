# The H-instantiation — bert-lenses#112, §4's remaining gap

**Status:** research + a working prototype, not a proof of anything about
`Circuit` itself. `lake build` is green on `Systems/Dynamics/CircuitHistory.lean`
(branch `research/112-h-instantiation`, worktree only — not merged, not added
to `Systems.lean`'s aggregator). **Zero `sorry`s in that file.** Every theorem's
axiom dependency is printed at the bottom of the file and repeated in §3 below.

This document is the plan bert-lenses#112 §4 named as future work: "instantiating
the general existence result at BERT's concrete state type." It reads
`docs/proposals/112-transition-functor.md` (bert-lenses repo, read-only) as the
accepted derivation and `Systems/Dynamics/Transition.lean` (this repo) as the
existing typed transition. Neither is re-derived here.

## 1. The carrier, stated precisely

```lean
structure Carrier (ι V : Type) where
  storage    : ι → V
  activity   : ι → V
  tick       : ℕ
  time       : V
  emitted    : V
  sunk       : V
  dissipated : V
```

`ι` is the circuit's fixed node index set; `V` is the numeric type the
Rust side calls `f32`, left abstract because no theorem in this file needs to
know which ordered field it is — Real vs. Rational is a decision for whoever
connects this to executable code, not a decision this file has to make.

**Justification, field by field, against proposal §1.2:**

- `storage`, `activity` (per node) — kept verbatim. These are exactly the two
  per-node fields `step_dt` both reads and writes every tick (§1.2, §1.3).
- `tick`, `time` (circuit-level) — kept verbatim. `time` is what forced-series
  lookups index by (§1.4), and Δt-refinement depends on it staying part of the
  carrier rather than becoming a derived quantity.
- `emitted`, `sunk`, `dissipated` (circuit-level ledger totals) — kept because
  the accepted target text (proposal §4, "storage, activity, tick, time,
  ledger totals") names them explicitly, and because they are genuinely
  mutated by `step_dt`'s write phase (`circuit.rs:1383-1384`, the
  `dissipated` residual computed at `circuit.rs:1331-1352`) — not read-only
  metadata.

**Justified exclusions, against proposal §1.6 and one judgment call not
settled by the sources:**

- The three circuit-level trace buffers (`history`, `ledger_history`,
  `wire_history`) — excluded by direct citation. §1.6 names these as the
  "conflates S with the accumulated trace H" finding and gives the "honest
  fix... state `S` as the fields in §1.2 minus the three trace buffers."
  This is not this document's judgment call; it is the proposal's own
  recommendation, applied.
- Per-node `total` and `spark` — excluded, but **this is a judgment call the
  source documents do not make explicitly** (§1.2 lists `total`/`spark`
  alongside `storage`/`activity` without flagging them as trace-buffer-like
  the way §1.6 flags the three circuit-level `Vec`s; the accepted target
  text in §4 simply omits them from its field list without arguing why).
  The argument made here: `total` (`circuit.rs:1402`, `+= sink_add[i]`,
  write-only, read only for the trace row at `circuit.rs:1439` and in tests)
  and `spark` (`circuit.rs:1377-1380`, an explicitly bounded sparkline
  buffer for UI display) are both **write-once-per-tick, never read back by
  the compute phase** (`circuit.rs:1098-1266`) — the same role §1.6
  identifies for the three flagged buffers. The asymmetry this creates —
  `total` excluded while `emitted`/`sunk`/`dissipated` are kept, despite all
  four being accumulators with the same read/write shape — is flagged in
  the Lean file's own doc comment rather than silently resolved, because
  resolving it one way or the other would be inventing a rule the sources
  don't state. If this asymmetry matters, the fix is a proposal amendment,
  not a Lean-file decision.

## 2. The statement to prove, and the degeneracy confronted honestly

### 2.1 What "final-coalgebra unfolding" means here

`Transition.lean`'s `kindCodomain .deterministic X = X`, so for a closed
descriptor (`inputType = outputType = Unit`) `Transition` is `Unit × S →
Unit × S`, i.e. `f : S → S` — `deterministicClosed f`. Read as a Mealy
functor over the descriptor's ports, `F(X) = (kindCodomain kind (outputType ×
X))^inputType`. Per the issue's 2026-07-25 comment ("SETTLED"), this Mealy
functor is a polynomial (container) functor for every kind, so a final
coalgebra (an M-type) exists unconditionally (Abbott–Altenkirch–Ghani 2005;
Gambino–Kock). **That existence result is cited here, not re-derived.**

### 2.2 The degeneracy, confronted rather than papered over

With `inputType = outputType = Unit` (the fully closed reading), `F = Id` and
the final `Id`-coalgebra is the one-point type `Unit` — every state is
bisimilar to every other, `H` collapses to a point, and "the history of a
run" carries zero information at the final-coalgebra level. This is not a
technicality; it is the correct answer to the question actually asked
("what does a closed deterministic system look like to an observer with no
output port") and it means **the naive statement of #112's adoption point 2
("H = final-coalgebra image of S under T") is false as the fully-closed
reading stands.**

The fix, per the same 2026-07-25 comment, is not a reformulation — it is the
**port**: setting `outputType := Carrier` (the identity observer) makes the
Mealy functor `F(X) = (Carrier × X)^Unit ≅ Carrier × X`, whose final
coalgebra is `ℕ → Carrier` (an output stream), non-degenerate for any
carrier with more than one distinguishable state. This is what
`Systems/Dynamics/CircuitHistory.lean` instantiates.

### 2.3 The theorem actually worth proving, in Lean syntax

```lean
theorem recordedHistory_is_coalgebra_prefix
    (f : Carrier ι V → Carrier ι V) (x0 : Carrier ι V) (n : ℕ) :
    recordedHistory f x0 n
      = (List.range (n + 1)).map
          (causalOutputOnly
            (cbeh (fun (_ : Unit) (t : Carrier ι V) => (t, f t)) x0))
```

where `recordedHistory f x0 n` is the abstracted `RecordedRun.history` — the
list of the first `n + 1` states starting from `x0` (index 0 is `x0` itself,
matching `RecordedRun::record`'s row-per-tick-plus-initial-row shape) — and
the right-hand side is the finite prefix of the **observable behaviour** of
`x0` under the final coalgebra of the identity-observed Mealy functor,
`cbeh` transported along the `Causal ≃ (ℕ → Carrier)` collapse
(`causalOutputOnly`).

**Why this is the right statement and not a restatement of the degenerate
one:** it is *not* "`H` = final coalgebra of the fully closed system" (false,
per §2.2) — it is "`H` = final coalgebra of the system **with the identity
observer attached**," which is exactly what #97's ratified reading ("`M = H`"
under the internal-trajectory interpretation) and the 2026-07-25 comment's
reconciliation clause both license: *"`H` = the final-coalgebra image of `S`
under `T`, for descriptors whose `outputType` separates the trajectories
claimed as mechanisms; the identity observer `outputType := Carrier` always
does."* This document's contribution is instantiating that clause's generic
`S` at BERT's concrete `Carrier ι V`, and connecting it by name to
`RecordedRun.history`.

## 3. The proof skeleton, lemma by lemma

All seven items below are in `Systems/Dynamics/CircuitHistory.lean`, ported
and specialized from the 2026-07-25 probe's §§1–2 (the M-type machinery in
that probe's §3 is deliberately NOT ported — it is not needed for this
statement, since the hand-built `Causal`/`cbeh` construction already gives
finality for `F X = (Carrier × X)^Unit` directly, no `PFunctor.M` needed).

| # | Lemma | Difficulty | Axiom cost (measured) |
|---|---|---|---|
| 1 | `Carrier`, `circuitDynamics`, `circuitTransition` — the type declarations | trivial (definitions, no proof obligation) | none |
| 2 | `recordedHistory`, `orbit` — the two list/stream definitions | trivial | none |
| 3 | `recordedHistory_eq_orbit_prefix` — `history` is the orbit's finite prefix | trivial (`rfl`) | **none** |
| 4 | `Causal`, `Causal.step`, `cbeh` — the final-coalgebra carrier and structure map, ported | trivial (definitions) | — |
| 5 | `cbeh_morphism` — `cbeh` is a coalgebra morphism | trivial (`rfl`) | **none** |
| 6 | `cbeh_unique` — finality: any coalgebra morphism into `Causal` equals `cbeh` | moderate (induction on the word, ported verbatim from the probe, unchanged) | **`Quot.sound`** (from `funext`, standard) |
| 7 | `causalOutputOnly` — `Causal ι V ≃ (ℕ → Carrier ι V)`, the stream collapse | moderate (an `Equiv`, two `left_inv`/`right_inv` proofs) | **`propext`, `Quot.sound`** (standard `Equiv`/`funext` cost, not new content) |
| 8 | `history_is_final_coalgebra_behaviour` — the target reconciliation, `orbit = observable behaviour` | moderate (induction on `n`, ported verbatim) | **`propext`, `Quot.sound`** |
| 9 | `recordedHistory_is_coalgebra_prefix` — the top-level chained theorem | trivial (`rw` of 3 and 8) | **`propext`, `Quot.sound`** |

**No `sorry` anywhere; `#print axioms` was run on every theorem and is
reproduced verbatim in the file's `Audit` section.** The `propext`/
`Quot.sound` cost is the ordinary price of `funext`-based equality proofs in
Lean 4 (both are core axioms, not Mathlib-classical baggage) — it is not the
`Classical.choice` dependency the 2026-07-25 comment flagged as incidental
for the M-type route (`PFunctor.M.children`). Making `V` abstract rather than
fixing it to `ℝ` was the change that removed `Classical.choice` entirely: an
earlier draft of this file hard-coded `V := ℝ` and picked up
`Classical.choice` transitively from Mathlib's Cauchy-sequence construction
of the reals, even in lemmas that never compute with a real number — that
was a cost of the *test instance*, not the theorem, and generalizing over
`V` was the fix, not a proof change.

**Total build time for the isolated target:** ~2 seconds once Mathlib's
`Data.Real.Basic`-adjacent dependency chain is warm (the file no longer
imports it — see above), confirming the content genuinely doesn't need the
real numbers.

## 4. What this lets the K≅2 program claim, claim-hygiene checked

**Machine-checked, today, in this worktree:** for ANY finite node index set
`ι`, ANY value type `V`, and ANY one-tick transition map `f : Carrier ι V →
Carrier ι V`, the sequence "the state after each tick, starting from `x0`"
(`recordedHistory`) is definitionally a finite prefix of the observable
behaviour of `x0` under the final coalgebra of the identity-observed,
closed-deterministic Mealy functor. This is a **general fact about the
`deterministicClosed` shape already in `Transition.lean`**, instantiated at
a carrier shaped like BERT's minimal circuit state — it is a theorem about
the *coalgebra reading of that shape*, not a theorem about
`bert_compose::Circuit` the Rust type.

**NOT machine-checked, and this document does not claim otherwise:**

- That BERT's actual `Circuit::step_dt(dt)` **is** an instance of `f` above
  — i.e., that the real Rust stepper, restricted to the fields this `Carrier`
  keeps, literally satisfies the type `Carrier ι V → Carrier ι V`. This
  document's `f` is an uninterpreted variable; connecting it to the real
  arithmetic (§1.3–§1.7 of the transition-functor proposal) is future work,
  explicitly out of scope here as it was in the proposal.
- That `RecordedRun::record_over`'s actual output (a `Vec` built by a `for`
  loop with an `algebraic_cycle` refusal, `run.rs:106-117`) matches
  `recordedHistory`'s total, unconditional shape. The refusal case (§1.6:
  `step_dt` no-ops rather than being undefined, when there is an anchorless
  cycle) is not modeled here; this file's `f` is assumed total.
- Anything about the tRNA pathology (§1.7) or the two engine defects it
  traces. Those are Rust engine defects independent of this theorem; a
  buggy `f` still satisfies `f : Carrier ι V → Carrier ι V` and still gets a
  well-defined (if wrong) `H`. Coalgebra shape does not certify semantic
  correctness — this was already the honest reading in §1.7's own
  ledger-arithmetic discussion (`final_balance ≈ 0` "certifies the ledger's
  own arithmetic is self-consistent, and nothing more") and it applies here
  too, one level up.
- Openness (C/N/E/B/G composition) — explicitly out of scope, carried
  verbatim from proposal §5.

**The honest one-paragraph claim:** *bert-lenses#112's Lean target — "H = the
final-coalgebra image of S under T" — is machine-checked as a general fact
about the closed-deterministic Mealy shape, instantiated at a carrier that
faithfully abstracts BERT's minimal circuit state (storage, activity, tick,
time, ledger totals — the three trace buffers excluded per the proposal's own
recommendation). What remains open is connecting the abstract transition map
`f` in this theorem to BERT's actual `step_dt` arithmetic; until that
connection is made, the result licenses "the shape of H is settled and proven
non-degenerate under the identity observer," not "BERT's recorded runs are
final-coalgebra unfoldings."*

## 5. Connection to Mobus's H (History)

Mobus's 8-tuple carries an `η` slot Mobus glosses informally as the system's
history — SSF's `Tuple.lean` names the slot but (per this repo's own
conservativity discipline) does not interpret it; `Systems/Dynamics/Record.lean`
explicitly defers the transition semantics of `τ` to #112 rather than typing
it prematurely (`Record.lean:19-26`).

What this file adds: **a machine-checked candidate reading of `η`/H**, for the
closed-deterministic case specifically — "the system's history" is the
observable behaviour of its initial state under the final coalgebra of its
one-tick map, with the identity observer attached. This is not a claim that
Mobus meant coalgebra theory; it is a claim that **when BERT's kernel commits
to `τ := Dynamics C` with `kind = deterministic`** (the `conservationExample`
descriptor already in `Record.lean`), the informal "H = History" gloss has a
precise, non-degenerate, machine-checked referent available to cite, and this
document names exactly which theorem that citation would point to
(`recordedHistory_is_coalgebra_prefix` above) — not a claim that the 8-tuple's
`η` slot has been formally identified with anything yet. That identification
(making `η` a typed field rather than an opaque slot) is a further step this
document does not take.

## 6. The three hardest open questions

1. **Does the totality assumption on `f` survive contact with
   `algebraic_cycle`?** §1.6 measures `step_dt` as "not total on the intended
   reading" — a no-op standing in for identity when the eval order fails.
   `RecordedRun::record_over` refuses at the caller level rather than
   recording a run of identity steps. This document's `orbit`/`cbeh`
   machinery assumes `f` is total (an unconditional self-map); whether the
   final-coalgebra reading should instead be built over a **partial** map
   (coalgebra of `S → Option S`, or restricted to the sub-type of
   non-anchorless-cycle circuits) is unresolved, and changes the theorem
   statement, not just its proof.
2. **Is the `total`/`spark` exclusion (§1) defensible, or does it need a
   proposal amendment first?** As flagged in §1, the source documents do not
   settle this; the argument given here (write-once-never-read-back) is
   this document's own, not a citation. If a future reviewer disagrees, the
   carrier's field list — not just this document's prose — needs to change.
3. **What is the right relationship between this file's `V`-generic
   `Carrier` and a real connection to `bert_compose::Circuit`'s actual `f32`
   fields?** `f32` has no direct Lean/Mathlib counterpart (Lean's `Float` is
   the closer analog, not `ℝ`, and floating-point semantics — rounding,
   non-associativity — could break lemmas that assumed an ordered field with
   exact arithmetic, though none of THIS file's lemmas depend on arithmetic
   properties of `V` at all, only on `f` being an arbitrary self-map). Future
   work connecting `f` to real `step_dt` code would need to settle whether
   the bridge goes through `ℝ` (idealized), `ℚ` (exact rationals, closer to
   engineering intent), or `Float` (bit-faithful but loses the clean algebra)
   — and this document takes no position.
