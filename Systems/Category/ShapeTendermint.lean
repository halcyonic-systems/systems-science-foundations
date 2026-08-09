/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.Data.Finite.Set
import Systems.Category.ShapeKlir
import Systems.Category.CommonCore

/-!
# Shape Category for Tendermint Consensus (fifth application probe)

The *shape category* `I_Tendermint` encodes the dependency structure of the
Tendermint BFT consensus algorithm as defined in Buchman, Kwon & Milošević,
"The latest gossip on BFT consensus" (arXiv:1807.04938) — the fifth
application encoded against the K ≅ 2 kernel, and the probe that tests
whether the chain/control family split (ShapeCosmos) is a LAYER split.

Pre-registered prediction (session 2026-08-08, logged before reading the
paper): Tendermint lands in the control family, ~70%. Outcome: the
prediction's mechanism is confirmed — the proposal ⇄ prevote feedback cycle
is textual — but the shape is richer than predicted: it carries BOTH
signatures at once, split across roles.

## Sources (arXiv:1807.04938, quotes verified verbatim 2026-08-08)

- §III: "The algorithm proceeds in rounds, where each round has a dedicated
  proposer." "Every round starts by a proposer suggesting a value with the
  PROPOSAL message."
- §III: "Processes exchange the following messages in Tendermint: PROPOSAL,
  PREVOTE and PRECOMMIT. The PROPOSAL message is used by the proposer of
  the current round to suggest a potential decision value."
- Algorithm 1, line 22: upon PROPOSAL from the proposer, a process
  broadcasts PREVOTE.
- Algorithm 1, lines 36–43 with §"variables": "any value v for which
  PROPOSAL and 2f + 1 of the corresponding PREVOTE messages are received in
  some round r is a possible decision value. The role of the validValue
  variable is to store the most recent possible decision value" — and
  Algorithm 1, lines 15–16: the proposer proposes validValue when it is
  set.
- Algorithm 1, line 36: upon PROPOSAL and 2f + 1 PREVOTE, a process
  broadcasts PRECOMMIT.
- Algorithm 1, line 49: the decision is taken upon PROPOSAL and 2f + 1
  PRECOMMIT.
- §II: "In the context of blockchain systems, for example, a value is not
  valid if it does not contain an appropriate hash of the last value
  (block) added to the blockchain."

## Construction

Positions are the roles the paper's sentences name:

- `process`: a validator (the paper's "process", weighted by voting power)
- `proposal`: a PROPOSAL message
- `prevote`: a PREVOTE message
- `precommit`: a PRECOMMIT message
- `value`: a potential decision value (a block, in the blockchain context)

Arrows point in the dependency direction (dependent → depended-on):

- `proposed_by : proposal → process` — every round starts by a proposer
  suggesting a value; the kernel arrow
- `proposes : proposal → value` — the PROPOSAL suggests a decision value
- `reproposes : proposal → prevote` — the proposer proposes validValue,
  which is set from 2f + 1 PREVOTEs (feedback, downward half)
- `on_proposal : prevote → proposal` — PREVOTE is broadcast upon PROPOSAL
  (feedback, upward half)
- `cast_by : prevote → process` — votes are counted by their senders'
  voting power
- `on_prevotes : precommit → prevote` — PRECOMMIT is broadcast upon
  2f + 1 PREVOTEs
- `committed_by : precommit → process`
- `decided_on : value → precommit` — a value is decided upon 2f + 1
  PRECOMMITs
- `chains : value → value` — a value is not valid unless it contains the
  hash of the last value added to the blockchain

## Encoding decisions

- The `chains` endo-arrow comes from §II's "in the context of blockchain
  systems, for example" clause — it is asserted for the blockchain
  instantiation of Tendermint (the paper's target context and the Cosmos
  Hub's use), not for abstract consensus. Removing it yields the shape of
  pure BFT consensus: control-family only.
- Heights and rounds are indices carried by every message, not named
  dependency roles; the round's one definitional dependency (its dedicated
  proposer) is carried by `proposed_by`. Timeouts, locking conditions, and
  the 2f + 1 thresholds are conditions on the dynamics, not shape (the
  Bunge `bondage_nonempty` analogue — finding 23's conditions-vs-data).
- Kernel choice: things ↦ process, relation ↦ proposal — the proposal is
  the round's organizing relation, predicated on its dedicated proposer.
  Alternative considered: votes also depend on senders (`cast_by`), so the
  kernel could enter through any message role; `proposal` is the one the
  paper's round-definition sentence names.

## The Finding (the layer split, made literal)

`ShapeCosmos` split the protocols into two families and predicted the split
is a layer split. Tendermint proves it within a single quiver
(`tendermint_layer_split`):

- **the control signature on the message roles**: proposal ⇄ prevote is a
  composite 2-cycle between distinct roles (`voteLoop`, Joslyn's pattern);
  no message role has an endo-arrow (`tendermint_endo_only_at_value`);
- **the chain signature on the decided role**: `chains : value → value` is
  a generating endo-arrow, and it sits at exactly the role consensus
  DECIDES — the block entering the ledger.

Consensus is a control loop; what it decides is a chain. The two families
of the protocol taxonomy are the two layers of one stack, and Tendermint is
the seam: the feedback machinery (how it decides) and the chain motif (what
it decides) are disjoint sub-shapes meeting at `proposes`/`decided_on`.

## Layered Status

Application witness, not a tradition entry. Not counted in the
eight-traditions headline.
-/

open CategoryTheory

/-- The five positions the paper's sentences name (arXiv:1807.04938, §II–III).

- `process`: a validator (the paper's "process", weighted by voting power)
- `proposal`: a PROPOSAL message
- `prevote`: a PREVOTE message
- `precommit`: a PRECOMMIT message
- `value`: a potential decision value (a block, in the blockchain context)
-/
inductive TendermintPosition
  | process
  | proposal
  | prevote
  | precommit
  | value
  deriving DecidableEq, Inhabited

/-- Generating morphisms of the Tendermint shape quiver, in the dependency
direction (dependent → depended-on).

One endo-arrow (`chains`, at the decided role) and one 2-cycle
(`reproposes`/`on_proposal`, between message roles): the chain and control
signatures in one quiver. -/
inductive TendermintArrow : TendermintPosition → TendermintPosition → Type
  | proposed_by  : TendermintArrow .proposal .process
  | proposes     : TendermintArrow .proposal .value
  | reproposes   : TendermintArrow .proposal .prevote
  | on_proposal  : TendermintArrow .prevote .proposal
  | cast_by      : TendermintArrow .prevote .process
  | on_prevotes  : TendermintArrow .precommit .prevote
  | committed_by : TendermintArrow .precommit .process
  | decided_on   : TendermintArrow .value .precommit
  | chains       : TendermintArrow .value .value

instance : Quiver TendermintPosition where
  Hom := TendermintArrow

/-- The shape category for Tendermint consensus: the free category on the
dependency quiver. 5 objects, 9 generating arrows — the densest protocol
shape so far, and the only one carrying both an endo-generator and a
distinct-role 2-cycle. -/
abbrev TendermintShape := Paths TendermintPosition

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Kernel embedding: I_Klir → I_Tendermint
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Embedding I_Klir into I_Tendermint: things ↦ process, relation ↦ proposal,
relation_on_things ↦ proposed_by.

"Every round starts by a proposer suggesting a value with the PROPOSAL
message" — the proposal is the round's organizing relation, predicated on
the process that proposes it. -/
def klirToTendermintPre : Prefunctor KlirPosition (Paths TendermintPosition) where
  obj | .things => .process | .relation => .proposal
  map | .relation_on_things => Quiver.Hom.toPath TendermintArrow.proposed_by

/-- The kernel embedding functor I_Klir ⥤ I_Tendermint. Faithfulness is
free: every functor out of I_Klir is faithful (CommonCore §Faithfulness). -/
def klirToTendermint : Paths KlirPosition ⥤ Paths TendermintPosition :=
  Paths.lift klirToTendermintPre

theorem klirToTendermint_obj_injective : Function.Injective klirToTendermintPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [klirToTendermintPre]

theorem klirToTendermint_faithful : klirToTendermint.Faithful :=
  faithful_of_subsingleton_hom _

-- ═══════════════════════════════════════════════════════════════════════════════
-- § The chain signature: the decided role chains
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The block chain of depth n: `chains` iterated n times — each value
hashing the last value added to the blockchain. -/
def blockChain : ℕ → Quiver.Path TendermintPosition.value TendermintPosition.value
  | 0 => .nil
  | n + 1 => (blockChain n).cons TendermintArrow.chains

theorem blockChain_length (n : ℕ) : (blockChain n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [blockChain, Quiver.Path.length_cons, ih]

theorem blockChain_injective : Function.Injective blockChain := by
  intro a b h
  have hlen := congrArg Quiver.Path.length h
  rw [blockChain_length, blockChain_length] at hlen
  exact hlen

/-- The chain hom-set `value ⟶ value` is infinite. -/
instance : Infinite (Quiver.Path TendermintPosition.value TendermintPosition.value) :=
  Infinite.of_injective blockChain blockChain_injective

-- ═══════════════════════════════════════════════════════════════════════════════
-- § The control signature: proposal ⇄ prevote, with no endo among messages
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The n-fold vote loop at `proposal`: (reproposes ; on_proposal)ⁿ —
proposals depend on the prevotes that validated an earlier value, and
prevotes depend on proposals. Joslyn's `nLoop` pattern between distinct
message roles. -/
def voteLoop : ℕ → Quiver.Path TendermintPosition.proposal TendermintPosition.proposal
  | 0 => .nil
  | n + 1 => ((voteLoop n).cons TendermintArrow.reproposes).cons TendermintArrow.on_proposal

theorem voteLoop_length (n : ℕ) : (voteLoop n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [voteLoop, Quiver.Path.length_cons, ih]; omega

theorem voteLoop_injective : Function.Injective voteLoop := by
  intro a b h
  have hlen := congrArg Quiver.Path.length h
  rw [voteLoop_length, voteLoop_length] at hlen
  omega

/-- The feedback hom-set `proposal ⟶ proposal` is infinite — through the
composite cycle, not through any endo-generator. -/
instance : Infinite (Quiver.Path TendermintPosition.proposal TendermintPosition.proposal) :=
  Infinite.of_injective voteLoop voteLoop_injective

/-- **The only endo-generator sits at the decided role.** Every generating
endo-arrow of I_Tendermint is `chains : value → value` — no message role and
no process role asserts a dependency on itself. -/
theorem tendermint_endo_only_at_value
    (X : TendermintPosition) : Nonempty (TendermintArrow X X) → X = .value := by
  rintro ⟨e⟩
  cases e
  rfl

/-- **No faithful functor I_Tendermint ⥤ I_Klir exists** — the pigeonhole
runs through the vote loop (the control signature suffices; the chain endo
is not needed). -/
theorem tendermint_no_faithful_functor_to_klir
    (F : TendermintShape ⥤ Paths KlirPosition) : ¬ F.Faithful := by
  intro hF
  haveI := hF
  have h01 : F.map (voteLoop 0) = F.map (voteLoop 1) :=
    Subsingleton.elim _ _
  have : voteLoop 0 = voteLoop 1 := F.map_injective h01
  simpa using voteLoop_injective this

-- ═══════════════════════════════════════════════════════════════════════════════
-- § The layer split, in one theorem
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Consensus is a control loop; what it decides is a chain.** One quiver
carries both taxonomy signatures, split across roles: the chain signature is
a generating endo-arrow at exactly the role consensus decides (`chains`),
while the message roles carry the control signature — an infinite hom-set at
`proposal` with no endo-generator anywhere but `value`. The chain/control
family split of the protocol taxonomy is a LAYER split within one stack. -/
theorem tendermint_layer_split :
    Nonempty (TendermintArrow .value .value) ∧
    IsEmpty (TendermintArrow .proposal .proposal) ∧
    Infinite (Quiver.Path TendermintPosition.proposal TendermintPosition.proposal) :=
  ⟨⟨.chains⟩, ⟨fun e => by cases e⟩, inferInstance⟩
