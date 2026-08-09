/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.Data.Finite.Set
import Systems.Category.ShapeKlir
import Systems.Category.CommonCore
import Systems.Category.ShapeBitcoin
import Systems.Category.ShapeEthereum

/-!
# Shape Category for Yakovenko's Solana (third application probe)

The *shape category* `I_Solana` encodes the dependency structure of Proof of
History as defined in Yakovenko, "Solana: A new architecture for a high
performance blockchain" (2017) — the third application encoded against the
K ≅ 2 kernel, and the probe that REFINES the Bitcoin/Ethereum classification:
the history locus is not a 2×2 over the kernel sides but a question of WHICH
ROLE carries the endo-generator.

## Sources

- Yakovenko (2017), §4 Proof of History: "Proof of History is a sequence of
  computation that can provide a way to cryptographically verify passage of
  time between two events." The function is run "in a sequence on a single
  core, its previous output as the current input, periodically recording the
  current output, and how many times its been called."
- Yakovenko (2017), §4: "Data can be timestamped into this sequence by
  appending the data (or a hash of some data) into the state of the
  function" — the recording of state, index, and data provides the
  timestamp.

Quotes verified verbatim against the published whitepaper PDF
(solana.com/solana-whitepaper.pdf), 2026-08-08.

## Construction

Positions are the roles the PoH definition names:

- `entry`: one periodically-recorded sample of the loop — a (count, hash)
  pair. ("entry"/"tick" is the docs-era name for the whitepaper's recorded
  sample; the naming decision is recorded here.)
- `event`: a piece of external data inserted into the sequence
- `sequence`: the Proof of History record itself

Arrows point in the dependency direction (dependent → depended-on):

- `chain_of : sequence → entry` — PoH IS a sequence of hash computations;
  the kernel arrow (the constitution reading, the exact analogue of
  Bitcoin's "a coin is a chain of digital signatures")
- `hash_prev : entry → entry` — the previous output is the next input;
  the endo-generator
- `records : entry → event` — an entry that timestamps an event appends the
  event's data into the state of the function, so the entry depends on the
  event

## The Refinement (the finding)

Under the kernel embedding (things ↦ entry, relation ↦ sequence), Solana's
endo-generator sits on the THINGS side — the same cell of the 2×2 as
Bitcoin. But the shape distinguishes them anyway, one level finer:

|          | chained role       | content role        | same position?    |
|----------|--------------------|---------------------|-------------------|
| Bitcoin  | transaction (endo) | transaction         | YES — coincide    |
| Ethereum | state (endo)       | transaction (thin)  | no — but state is the relation |
| Solana   | entry (endo)       | event (thin)        | no — both things-side |

In Bitcoin the recorded content and the chain are the SAME position: what
chains is what the ledger is about (value transfers). In Solana they are
DIFFERENT positions: the chain is contentless computation (a clock), and the
content hangs off it without chaining (`solana_event_self`). This is
Yakovenko's own pitch — the clock is separated from the content and runs
before consensus — rendered as shape: **Solana is the first protocol where
the chained role and the content role are distinct positions on the same
side of the kernel.** The classification invariant is therefore not "which
kernel side chains" but "which role chains, and whether it is the content":
value-things (Bitcoin), state-relation (Ethereum), clock-things (Solana).

Per the layer discipline: leaders, verifiers, Proof of Stake, and consensus
are dynamics-layer commitments, scoped out as PoW and the EVM were.

## Layered Status

Application witness, not a tradition entry. Not counted in the
eight-traditions headline.
-/

open CategoryTheory

/-- The three positions the PoH definition names (Yakovenko 2017).

- `entry`: one recorded sample of the hash loop — a (count, hash) pair
- `event`: a piece of external data inserted into the sequence
- `sequence`: the Proof of History record itself
-/
inductive SolanaPosition
  | entry
  | event
  | sequence
  deriving DecidableEq, Inhabited

/-- Generating morphisms of the Solana shape quiver, in the dependency
direction (dependent → depended-on).

`hash_prev` is the endo-generator — and note which role carries it: the
ENTRY (the tick of the clock), not the event. The content role has no loop. -/
inductive SolanaArrow : SolanaPosition → SolanaPosition → Type
  | chain_of  : SolanaArrow .sequence .entry
  | hash_prev : SolanaArrow .entry .entry
  | records   : SolanaArrow .entry .event

instance : Quiver SolanaPosition where
  Hom := SolanaArrow

/-- The shape category for Yakovenko's Proof of History: the free category on
the dependency quiver. 3 objects, 3 generating arrows, one endo-arrow at the
clock role. The sparsest protocol shape so far — Solana's definitional core
is a single self-hashing chain with content attached. -/
abbrev SolanaShape := Paths SolanaPosition

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Kernel embedding: I_Klir → I_Solana
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Embedding I_Klir into I_Solana: things ↦ entry, relation ↦ sequence,
relation_on_things ↦ chain_of.

The constitution reading, exactly as for Bitcoin: PoH is defined AS a
sequence of hash computations, so the sequence is the relation predicated on
the entries that constitute it. -/
def klirToSolanaPre : Prefunctor KlirPosition (Paths SolanaPosition) where
  obj | .things => .entry | .relation => .sequence
  map | .relation_on_things => Quiver.Hom.toPath SolanaArrow.chain_of

/-- The kernel embedding functor I_Klir ⥤ I_Solana. Faithfulness is free:
every functor out of I_Klir is faithful (CommonCore §Faithfulness). -/
def klirToSolana : Paths KlirPosition ⥤ Paths SolanaPosition :=
  Paths.lift klirToSolanaPre

theorem klirToSolana_obj_injective : Function.Injective klirToSolanaPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [klirToSolanaPre]

theorem klirToSolana_faithful : klirToSolana.Faithful :=
  faithful_of_subsingleton_hom _

-- ═══════════════════════════════════════════════════════════════════════════════
-- § The endo-generator: the tick chain is an infinite hom-set
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The tick chain of depth n: `hash_prev` iterated n times — n steps of
verifiable time. -/
def tickChain : ℕ → Quiver.Path SolanaPosition.entry SolanaPosition.entry
  | 0 => .nil
  | n + 1 => (tickChain n).cons SolanaArrow.hash_prev

theorem tickChain_length (n : ℕ) : (tickChain n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [tickChain, Quiver.Path.length_cons, ih]

/-- Distinct tick depths give distinct paths (their lengths differ). -/
theorem tickChain_injective : Function.Injective tickChain := by
  intro a b h
  have hlen := congrArg Quiver.Path.length h
  rw [tickChain_length, tickChain_length] at hlen
  exact hlen

/-- The tick hom-set `entry ⟶ entry` is infinite. -/
instance : Infinite (Quiver.Path SolanaPosition.entry SolanaPosition.entry) :=
  Infinite.of_injective tickChain tickChain_injective

/-- **No faithful functor I_Solana ⥤ I_Klir exists** — the same pigeonhole
as the other two protocols, through the tick loop. -/
theorem solana_no_faithful_functor_to_klir
    (F : SolanaShape ⥤ Paths KlirPosition) : ¬ F.Faithful := by
  intro hF
  haveI := hF
  have h01 : F.map (tickChain 0) = F.map (tickChain 1) :=
    Subsingleton.elim _ _
  have : tickChain 0 = tickChain 1 := F.map_injective h01
  simpa using tickChain_injective this

-- ═══════════════════════════════════════════════════════════════════════════════
-- § The refinement: the clock chains, the content does not
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The `sequence` hom-set is trivial: nothing targets `sequence`.
(The relation-image is thin, as for Bitcoin's `coin`.) -/
theorem solana_sequence_self
    (p : Quiver.Path SolanaPosition.sequence SolanaPosition.sequence) : p = .nil := by
  cases p with
  | nil => rfl
  | cons _ e => exact nomatch e

/-- No path leads from `event` back into the tick loop: `event` is a sink. -/
theorem solana_no_path_event_entry :
    ∀ (p : Quiver.Path SolanaPosition.event SolanaPosition.entry), False
  | .cons p e => match e with
    | .hash_prev => solana_no_path_event_entry p

/-- **The content hom-set is trivial — events do not chain.** The only arrow
into `event` comes from `entry`, and `event` (a sink) cannot reach the loop.
The direct contrast with Bitcoin, where the content role (`transaction`) IS
the chained role: Solana's chain is a contentless clock, and what the ledger
is about hangs off it without self-reference. -/
theorem solana_event_self
    (p : Quiver.Path SolanaPosition.event SolanaPosition.event) : p = .nil := by
  cases p with
  | nil => rfl
  | cons p e =>
    cases e with
    | records => exact (solana_no_path_event_entry p).elim

/-- **The clock/content separation.** Solana's chained role (`entry`) has an
infinite self-hom while its content role (`event`) is trivial — whereas in
Bitcoin the two roles are the same position (`transaction`), so its content
provably chains. Three protocols, three history loci: value-things
(Bitcoin), state-relation (Ethereum: `protocol_history_locus_separation`),
clock-things (Solana). -/
theorem solana_clock_content_separation :
    (Infinite (Quiver.Path SolanaPosition.entry SolanaPosition.entry) ∧
      ∀ p : Quiver.Path SolanaPosition.event SolanaPosition.event, p = .nil) ∧
    Infinite (Quiver.Path BitcoinPosition.transaction BitcoinPosition.transaction) :=
  ⟨⟨inferInstance, solana_event_self⟩, inferInstance⟩
