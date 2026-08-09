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
# Shape Category for Nakamoto's Bitcoin (application probe)

The *shape category* `I_Bitcoin` encodes the dependency structure of the Bitcoin
protocol as defined in Nakamoto, "Bitcoin: A Peer-to-Peer Electronic Cash System"
(2008) — the first APPLICATION encoded against the K ≅ 2 kernel, probing whether
the tradition-encoding template extends from systems-science source texts to a
protocol specification.

## Sources

- Nakamoto (2008), §2 Transactions: "We define an electronic coin as a chain of
  digital signatures. Each owner transfers the coin to the next by digitally
  signing a hash of the previous transaction and the public key of the next
  owner and adding these to the end of the coin."
- Nakamoto (2008), §3 Timestamp Server: the server "takes a hash of a block of
  items to be timestamped"; "each timestamp includes the previous timestamp in
  its hash, forming a chain."

## Construction

Positions are the roles Nakamoto's own definitional sentences name:

- `owner`: a public key ("the next owner", §2)
- `transaction`: one signature step in a coin (§2)
- `coin`: the chain of digital signatures — Nakamoto's definitional sentence (§2)
- `block`: a hashed collection of items to be timestamped (§3)

Arrows point in the dependency direction (dependent → depended-on, the
convention of `relation_on_things : relation → things`):

- `chain_of : coin → transaction` — a coin IS a chain of signatures (§2);
  the kernel arrow
- `hash_prev : transaction → transaction` — each transfer signs "a hash of the
  previous transaction" (§2)
- `pays : transaction → owner` — and "the public key of the next owner" (§2)
- `timestamps : block → transaction` — a block is a hash over items (§3)
- `block_prev : block → block` — "each timestamp includes the previous
  timestamp in its hash" (§3)

## Layered Status (application witness, not tradition #9)

Bitcoin is not a systems tradition and is NOT counted in the eight-traditions
headline. It enters the landscape as an application probe with two findings:

1. **The kernel embeds** (`klirToBitcoin`): things ↦ transaction,
   relation ↦ coin, along Nakamoto's own definitional sentence. Injective on
   objects, faithful (free, since I_Klir is thin).

2. **The embedding does not reverse** (`bitcoin_no_faithful_functor_to_klir`),
   and the obstruction is Bitcoin's signature structural motif: hash-chaining
   is role-level SELF-reference. `hash_prev` and `block_prev` are generating
   endo-arrows — the quiver itself asserts a dependency of a role on itself.
   No encoded tradition's quiver has an endo-generator: Joslyn's infinite
   hom-set (`JoslynIncomparability`) arises from a COMPOSITE 2-cycle of two
   generators, while Bitcoin asserts the loop as a single generator. At the
   quiver level — where the repaired maximality statement lives
   (`SharedPrimitive.connected_is_single_arrow`) — this makes Bitcoin a
   genuinely new shape, not a ride-along.

Bitcoin also fails the Joslyn obstruction (transaction has out-degree 2:
`hash_prev`, `pays`), consistent with its status as an application instance
rather than a kernel candidate.

## Encoding decisions (recorded per the faithfulness discipline)

- `coin`, not "ledger" or "UTXO set": Nakamoto's §2 sentence is the definition
  the encoding is drawn from; UTXO vocabulary postdates the paper.
- The mining/consensus layer (proof-of-work, longest-chain rule, §4–5) is a
  DYNAMICS commitment (which chain extension wins), not a dependency-shape
  commitment, and is deliberately not encoded here — the analogue of Willems'
  composition layer being out of scope for I_Willems.
- `timestamps : block → transaction` reads §3's "block of items" with items =
  transactions, which §5 makes explicit ("new transactions are broadcast …
  each node collects new transactions into a block").
-/

open CategoryTheory

/-- The four positions Nakamoto's definitional sentences name (2008, §2–3).

- `owner`: a public key
- `transaction`: one signature step in a coin
- `coin`: the chain of digital signatures (§2, the definition)
- `block`: a hashed collection of items to be timestamped (§3)
-/
inductive BitcoinPosition
  | owner
  | transaction
  | coin
  | block
  deriving DecidableEq, Inhabited

/-- Generating morphisms of the Bitcoin shape quiver, in the dependency
direction (dependent → depended-on).

`hash_prev` and `block_prev` are generating ENDO-arrows — Nakamoto's
hash-chaining motif asserts a role's dependency on itself. No encoded
tradition's quiver has one. -/
inductive BitcoinArrow : BitcoinPosition → BitcoinPosition → Type
  | chain_of   : BitcoinArrow .coin .transaction
  | hash_prev  : BitcoinArrow .transaction .transaction
  | pays       : BitcoinArrow .transaction .owner
  | timestamps : BitcoinArrow .block .transaction
  | block_prev : BitcoinArrow .block .block

instance : Quiver BitcoinPosition where
  Hom := BitcoinArrow

/-- The shape category for Nakamoto's Bitcoin: the free category on the
dependency quiver. 4 objects, 5 generating arrows, two of them endo-arrows —
the first shape in the landscape whose QUIVER is not loop-free. -/
abbrev BitcoinShape := Paths BitcoinPosition

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Kernel embedding: I_Klir → I_Bitcoin
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Embedding I_Klir into I_Bitcoin: things ↦ transaction, relation ↦ coin,
relation_on_things ↦ chain_of.

The assignment follows Nakamoto's definitional sentence directly: "an
electronic coin [is] a chain of digital signatures" — the coin is the relation
predicated on the transactions that constitute it. -/
def klirToBitcoinPre : Prefunctor KlirPosition (Paths BitcoinPosition) where
  obj | .things => .transaction | .relation => .coin
  map | .relation_on_things => Quiver.Hom.toPath BitcoinArrow.chain_of

/-- The kernel embedding functor I_Klir ⥤ I_Bitcoin. Faithfulness is free:
every functor out of I_Klir is faithful (CommonCore §Faithfulness). -/
def klirToBitcoin : Paths KlirPosition ⥤ Paths BitcoinPosition :=
  Paths.lift klirToBitcoinPre

theorem klirToBitcoin_obj_injective : Function.Injective klirToBitcoinPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [klirToBitcoinPre]

theorem klirToBitcoin_faithful : klirToBitcoin.Faithful :=
  faithful_of_subsingleton_hom _

-- ═══════════════════════════════════════════════════════════════════════════════
-- § The endo-generator: spend ancestry is an infinite hom-set
--
-- Iterating `hash_prev` walks a coin's spend ancestry: each transfer signs the
-- hash of the previous transaction, so a path of length n is "the transaction
-- n transfers back." Distinct depths are distinct paths, so the hom-set
-- transaction ⟶ transaction is infinite — directly from ONE generating arrow,
-- unlike Joslyn's composite feedback 2-cycle (JoslynIncomparability.nLoop).
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The spend-ancestry path of depth n: `hash_prev` iterated n times. -/
def spendAncestry : ℕ → Quiver.Path BitcoinPosition.transaction BitcoinPosition.transaction
  | 0 => .nil
  | n + 1 => (spendAncestry n).cons BitcoinArrow.hash_prev

theorem spendAncestry_length (n : ℕ) : (spendAncestry n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [spendAncestry, Quiver.Path.length_cons, ih]

/-- Distinct ancestry depths give distinct paths (their lengths differ). -/
theorem spendAncestry_injective : Function.Injective spendAncestry := by
  intro a b h
  have hlen := congrArg Quiver.Path.length h
  rw [spendAncestry_length, spendAncestry_length] at hlen
  exact hlen

/-- The spend-ancestry hom-set `transaction ⟶ transaction` is infinite. -/
instance : Infinite (Quiver.Path BitcoinPosition.transaction BitcoinPosition.transaction) :=
  Infinite.of_injective spendAncestry spendAncestry_injective

/-- I_Bitcoin is not thin: the identity and one step of spend ancestry are
distinct parallel morphisms. I_Klir, by contrast, is thin
(`klir_path_subsingleton`). -/
theorem bitcoin_shape_not_thin :
    ∃ p q : Quiver.Path BitcoinPosition.transaction BitcoinPosition.transaction, p ≠ q :=
  ⟨spendAncestry 0, spendAncestry 1, fun h => by simpa using spendAncestry_injective h⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- § The asymmetry: the kernel embeds into Bitcoin, Bitcoin cannot embed back
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **No faithful functor I_Bitcoin ⥤ I_Klir exists.** Faithfulness would
inject the infinite spend-ancestry hom-set into a subsingleton hom-set of the
thin kernel. Together with `klirToBitcoin`, the embedding is strictly one-way:
Bitcoin carries the kernel's one dependency, plus structure (hash-chaining
self-reference) the kernel cannot absorb. -/
theorem bitcoin_no_faithful_functor_to_klir
    (F : BitcoinShape ⥤ Paths KlirPosition) : ¬ F.Faithful := by
  intro hF
  haveI := hF
  have h01 : F.map (spendAncestry 0) = F.map (spendAncestry 1) :=
    Subsingleton.elim _ _
  have : spendAncestry 0 = spendAncestry 1 := F.map_injective h01
  simpa using spendAncestry_injective this
