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

/-!
# Shape Category for Wood's Ethereum (second application probe)

The *shape category* `I_Ethereum` encodes the dependency structure of Ethereum
as defined in Wood, "Ethereum: A Secure Decentralised Generalised Transaction
Ledger" (the Yellow Paper, 2014) — the second application encoded against the
K ≅ 2 kernel, and the SEPARATING INSTANCE for the protocol program: the same
template that carried Bitcoin produces a provably different shape.

## Sources

- Wood (2014), §2: Ethereum "can be viewed as a transaction-based state
  machine" — a genesis state incrementally morphed by executing transactions;
  the state-transition function σ_{t+1} ≡ Υ(σ_t, T).
- Wood (2014), §4.1 World State: "a mapping between addresses (160-bit
  identifiers) and account states."
- Wood (2014), §4.2: a transaction is a single cryptographically-signed
  instruction constructed by an actor external to the scope of Ethereum.
- Wood (2014), §4.3: a block comprises a header and its transactions; each
  header carries the parent block's hash.

## Construction

Positions are the roles Wood's definitional sentences name:

- `actor`: the external signer (§4.2)
- `account`: an account state, keyed by address (§4.1)
- `transaction`: one signed instruction (§4.2)
- `state`: the world state σ — the mapping over accounts (§4.1)
- `block`: header + comprised transactions (§4.3)

Arrows point in the dependency direction (dependent → depended-on):

- `maps_accounts : state → account` — σ IS a mapping over account states
  (§4.1); the kernel arrow
- `prior_state : state → state` — σ_{t+1} depends on σ_t (§2, Υ)
- `applies : state → transaction` — and on the transaction applied (§2, Υ)
- `signed_by : transaction → actor` — signed by an external actor (§4.2)
- `includes : block → transaction` — a block comprises transactions (§4.3)
- `parent : block → block` — the parent-hash chain (§4.3)

## The Separation (the finding)

Both protocols carry the kernel and both refuse to reverse it, but their
endo-generators sit on OPPOSITE SIDES of the kernel embedding:

|          | things-image                | relation-image          |
|----------|-----------------------------|-------------------------|
| Bitcoin  | transaction — endo, infinite| coin — thin             |
| Ethereum | account — thin              | state — endo, infinite  |

Bitcoin's §2 sentence puts the history on the things: a coin IS a chain of
signatures, so `hash_prev` loops at `transaction` while `coin` has trivial
self-homs (`bitcoin_coin_self`). Wood's §2 sentence puts the history on the
relation: the world state is morphed in place, so `prior_state` loops at
`state` while `account` and `transaction` have trivial self-homs
(`ethereum_account_self`, `ethereum_transaction_self`). This is the
UTXO/account-model distinction rendered as machine-checked shape: **UTXO
chains accrete history on the things; the account model accretes history on
the relation.** In Ethereum, a transaction never references a prior
transaction — replay protection lives in the account nonce (§4.1), i.e. in
the state, exactly where the shape says it must.

Per the layer discipline (Willems, companion 21): this is a shape-layer
claim. Gas, the EVM, and consensus are dynamics-layer commitments and are
deliberately not encoded, as proof-of-work was not for Bitcoin.

## Layered Status

Application witness, not a tradition entry. Not counted in the
eight-traditions headline.
-/

open CategoryTheory

/-- The five positions Wood's definitional sentences name (2014, §2, §4.1–4.3).

- `actor`: the external signer
- `account`: an account state, keyed by address
- `transaction`: one signed instruction
- `state`: the world state σ — the mapping over accounts
- `block`: header + comprised transactions
-/
inductive EthereumPosition
  | actor
  | account
  | transaction
  | state
  | block
  deriving DecidableEq, Inhabited

/-- Generating morphisms of the Ethereum shape quiver, in the dependency
direction (dependent → depended-on).

`prior_state` and `parent` are the generating endo-arrows. Note where
`prior_state` sits: on the STATE, not the transaction — Wood's state machine
morphs σ in place, it does not chain instructions. -/
inductive EthereumArrow : EthereumPosition → EthereumPosition → Type
  | maps_accounts : EthereumArrow .state .account
  | prior_state   : EthereumArrow .state .state
  | applies       : EthereumArrow .state .transaction
  | signed_by     : EthereumArrow .transaction .actor
  | includes      : EthereumArrow .block .transaction
  | parent        : EthereumArrow .block .block

instance : Quiver EthereumPosition where
  Hom := EthereumArrow

/-- The shape category for Wood's Ethereum: the free category on the
dependency quiver. 5 objects, 6 generating arrows, two of them endo-arrows —
like I_Bitcoin, the quiver is not loop-free; unlike I_Bitcoin, the
transaction-role loop is absent and the state-role loop is present. -/
abbrev EthereumShape := Paths EthereumPosition

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Kernel embedding: I_Klir → I_Ethereum
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Embedding I_Klir into I_Ethereum: things ↦ account, relation ↦ state,
relation_on_things ↦ maps_accounts.

The assignment follows Wood's §4.1 definitional sentence directly: the world
state is "a mapping between addresses and account states" — the state is the
relation predicated on the accounts it maps. -/
def klirToEthereumPre : Prefunctor KlirPosition (Paths EthereumPosition) where
  obj | .things => .account | .relation => .state
  map | .relation_on_things => Quiver.Hom.toPath EthereumArrow.maps_accounts

/-- The kernel embedding functor I_Klir ⥤ I_Ethereum. Faithfulness is free:
every functor out of I_Klir is faithful (CommonCore §Faithfulness). -/
def klirToEthereum : Paths KlirPosition ⥤ Paths EthereumPosition :=
  Paths.lift klirToEthereumPre

theorem klirToEthereum_obj_injective : Function.Injective klirToEthereumPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [klirToEthereumPre]

theorem klirToEthereum_faithful : klirToEthereum.Faithful :=
  faithful_of_subsingleton_hom _

-- ═══════════════════════════════════════════════════════════════════════════════
-- § The endo-generator: state history is an infinite hom-set
--
-- Iterating `prior_state` walks the state machine's history: σ_t, σ_{t-1}, …
-- back toward genesis. Distinct depths are distinct paths, so the hom-set
-- state ⟶ state is infinite — the mirror image of Bitcoin's spend ancestry,
-- relocated from the things to the relation.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The state-history path of depth n: `prior_state` iterated n times. -/
def stateHistory : ℕ → Quiver.Path EthereumPosition.state EthereumPosition.state
  | 0 => .nil
  | n + 1 => (stateHistory n).cons EthereumArrow.prior_state

theorem stateHistory_length (n : ℕ) : (stateHistory n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [stateHistory, Quiver.Path.length_cons, ih]

/-- Distinct history depths give distinct paths (their lengths differ). -/
theorem stateHistory_injective : Function.Injective stateHistory := by
  intro a b h
  have hlen := congrArg Quiver.Path.length h
  rw [stateHistory_length, stateHistory_length] at hlen
  exact hlen

/-- The state-history hom-set `state ⟶ state` is infinite. -/
instance : Infinite (Quiver.Path EthereumPosition.state EthereumPosition.state) :=
  Infinite.of_injective stateHistory stateHistory_injective

/-- **No faithful functor I_Ethereum ⥤ I_Klir exists** — the same pigeonhole
as Bitcoin's, through the state loop instead of the spend loop. -/
theorem ethereum_no_faithful_functor_to_klir
    (F : EthereumShape ⥤ Paths KlirPosition) : ¬ F.Faithful := by
  intro hF
  haveI := hF
  have h01 : F.map (stateHistory 0) = F.map (stateHistory 1) :=
    Subsingleton.elim _ _
  have : stateHistory 0 = stateHistory 1 := F.map_injective h01
  simpa using stateHistory_injective this

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Separation: the endo-generators sit on opposite sides of the kernel
--
-- Bitcoin: things-image (transaction) infinite, relation-image (coin) thin.
-- Ethereum: things-image (account) thin, relation-image (state) infinite.
-- The thin halves are proved here; the infinite halves are the two Infinite
-- instances (ShapeBitcoin and above).
-- ═══════════════════════════════════════════════════════════════════════════════

/-- No path leads from `account` into the state loop: `account` is a sink, so
nothing leaves it at all. Auxiliary to `ethereum_account_self`. -/
theorem ethereum_no_path_account_state :
    ∀ (p : Quiver.Path EthereumPosition.account EthereumPosition.state), False
  | .cons p e => match e with
    | .prior_state => ethereum_no_path_account_state p

/-- The `account` hom-set is trivial: Ethereum's things carry no history.
The only arrow into `account` comes from `state`, and `account` (a sink)
cannot reach `state`. Contrast `spendAncestry`: Bitcoin's things-image is
where the loop lives. -/
theorem ethereum_account_self
    (p : Quiver.Path EthereumPosition.account EthereumPosition.account) : p = .nil := by
  cases p with
  | nil => rfl
  | cons p e =>
    cases e with
    | maps_accounts => exact (ethereum_no_path_account_state p).elim

/-- No path leads from `transaction` back into the state loop. -/
theorem ethereum_no_path_transaction_state :
    ∀ (p : Quiver.Path EthereumPosition.transaction EthereumPosition.state), False
  | .cons p e => match e with
    | .prior_state => ethereum_no_path_transaction_state p

/-- No path leads from `transaction` into the block chain. -/
theorem ethereum_no_path_transaction_block :
    ∀ (p : Quiver.Path EthereumPosition.transaction EthereumPosition.block), False
  | .cons p e => match e with
    | .parent => ethereum_no_path_transaction_block p

/-- **The transaction hom-set is trivial — Ethereum transactions do not
chain.** Every arrow into `transaction` comes from `state` or `block`, and
`transaction` reaches neither (its only out-arrow targets the `actor` sink).
The direct contrast with Bitcoin, where `hash_prev` makes this same-named
role's hom-set infinite: replay protection lives in the account nonce (§4.1)
— in the state — exactly where the shape relocates the history. -/
theorem ethereum_transaction_self
    (p : Quiver.Path EthereumPosition.transaction EthereumPosition.transaction) :
    p = .nil := by
  cases p with
  | nil => rfl
  | cons p e =>
    cases e with
    | applies => exact (ethereum_no_path_transaction_state p).elim
    | includes => exact (ethereum_no_path_transaction_block p).elim

-- The kernel images, pinned by `rfl` (stated at the prefunctor level to stay
-- in the base quiver — in `Paths V`, object ascription grabs the wrong
-- Quiver instance; see the JoslynIncomparability engineering note):

theorem klirToBitcoin_things_is_transaction :
    klirToBitcoinPre.obj .things = BitcoinPosition.transaction := rfl
theorem klirToBitcoin_relation_is_coin :
    klirToBitcoinPre.obj .relation = BitcoinPosition.coin := rfl
theorem klirToEthereum_things_is_account :
    klirToEthereumPre.obj .things = EthereumPosition.account := rfl
theorem klirToEthereum_relation_is_state :
    klirToEthereumPre.obj .relation = EthereumPosition.state := rfl

/-- **The separation.** The infinite self-hom sits at `transaction` for
Bitcoin and at `state` for Ethereum, and the opposite kernel image is trivial
in each — by the four `rfl` lemmas above, these four positions are exactly
the things/relation images of the two kernel embeddings: UTXO chains accrete
history on the things; the account model accretes it on the relation. -/
theorem protocol_history_locus_separation :
    (Infinite (Quiver.Path BitcoinPosition.transaction BitcoinPosition.transaction) ∧
      ∀ p : Quiver.Path BitcoinPosition.coin BitcoinPosition.coin, p = .nil) ∧
    (Infinite (Quiver.Path EthereumPosition.state EthereumPosition.state) ∧
      ∀ p : Quiver.Path EthereumPosition.account EthereumPosition.account, p = .nil) :=
  ⟨⟨inferInstance, bitcoin_coin_self⟩, ⟨inferInstance, ethereum_account_self⟩⟩
