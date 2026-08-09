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
# Shape Category for Popov's Tangle (sixth application probe)

The *shape category* `I_Iota` encodes the dependency structure of the IOTA
Tangle as defined in Popov, "The Tangle" (v1.4.3, 2018) — the sixth
application encoded against the K ≅ 2 kernel, and the probe that settles the
DAG question: **the DAG ledger is not a fourth cell of the taxonomy.** It is
Bitcoin's cell with doubled arrows — the chain family admits a BRANCHING
parameter, and that parameter is the DAG/chain distinction.

## Sources (Popov v1.4.3, quotes verified verbatim 2026-08-08)

- Abstract: "the tangle, a directed acyclic graph (DAG) for storing
  transactions. The tangle naturally succeeds the blockchain as its next
  evolutionary step."
- §1: "The transactions issued by nodes constitute the site set of the
  tangle graph, which is the ledger for storing transactions."
- §1: "when a new transaction arrives, it must approve two previous
  transactions. these approvals are represented by directed edges." Footnote
  1 generalizes: "approve k other transactions for a general k ≥ 2."
- §1: "nodes are entities that issue and validate transactions."

## Construction

Positions are the roles Popov's sentences name:

- `node`: an entity that issues and validates transactions
- `transaction`: a site of the tangle graph
- `tangle`: the DAG itself — the ledger

Arrows point in the dependency direction (dependent → depended-on):

- `stores : tangle → transaction` — the transactions constitute the site
  set of the tangle, which is the ledger; the kernel arrow (constitution
  reading, exactly Bitcoin's "a coin is a chain of digital signatures")
- `approves₁, approves₂ : transaction → transaction` — a new transaction
  must approve TWO previous transactions: two parallel generating
  endo-arrows, one per approval slot
- `issued_by : transaction → node` — transactions are issued by nodes

## Encoding decisions

- Two parallel endo-arrows, not one: Popov's definitional sentence asserts
  two approvals per transaction as separate edges of the tangle graph.
  Footnote 1's "k ≥ 2" makes branching a protocol parameter; the shape
  encodes the definitional default k = 2.
- "Tips" (unapproved transactions) and the genesis transaction are
  instance-level features — a tip is a transaction with no approvers yet,
  the genesis a distinguished transaction — not dependency roles; neither
  is a position.
- "Acyclic" in DAG is an instance-level constraint on the transaction
  graph; at the role level the quiver has self-loops, exactly as Bitcoin's
  does. Same role/instance distinction as Cosmos's acyclic hub topology
  over a cyclic role dependency.
- The MCMC tip-selection algorithm is dynamics-layer (it selects WHICH two
  transactions; the shape records THAT two are approved), scoped out as
  PoW, the EVM, and leader selection were.

## The Finding

Under the kernel embedding (things ↦ transaction, relation ↦ tangle), IOTA
lands in exactly Bitcoin's cell: content-things locus, chained role =
content role, relation-image thin (`iota_tangle_self`). What separates them
is machine-checked one level finer (`iota_branching_separation`): Bitcoin's
quiver has a UNIQUE endo-generator at the chained role
(`bitcoin_endo_unique`), while IOTA asserts TWO DISTINCT parallel
endo-generators. The DAG/chain distinction is therefore not a new history
locus but a branching width within the chain family — the taxonomy after
six probes: two families (chain/control), three loci within the chain
family (value-things, state-relation, clock-things), and a branching
parameter within each locus (Bitcoin k = 1, IOTA k = 2).

## Layered Status

Application witness, not a tradition entry. Not counted in the
eight-traditions headline.
-/

open CategoryTheory

/-- The three positions Popov's sentences name (v1.4.3, §1).

- `node`: an entity that issues and validates transactions
- `transaction`: a site of the tangle graph
- `tangle`: the DAG itself — the ledger
-/
inductive IotaPosition
  | node
  | transaction
  | tangle
  deriving DecidableEq, Inhabited

/-- Generating morphisms of the IOTA shape quiver, in the dependency
direction (dependent → depended-on).

`approves₁` and `approves₂` are two PARALLEL generating endo-arrows — one
per approval slot of Popov's "it must approve two previous transactions."
The first parallel pair of generators in the landscape. -/
inductive IotaArrow : IotaPosition → IotaPosition → Type
  | stores    : IotaArrow .tangle .transaction
  | approves₁ : IotaArrow .transaction .transaction
  | approves₂ : IotaArrow .transaction .transaction
  | issued_by : IotaArrow .transaction .node

instance : Quiver IotaPosition where
  Hom := IotaArrow

/-- The shape category for Popov's Tangle: the free category on the
dependency quiver. 3 objects, 4 generating arrows, two of them parallel
endo-arrows at the content role — Bitcoin's shape with the chain motif
doubled. -/
abbrev IotaShape := Paths IotaPosition

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Kernel embedding: I_Klir → I_Iota
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Embedding I_Klir into I_Iota: things ↦ transaction, relation ↦ tangle,
relation_on_things ↦ stores.

The constitution reading, exactly Bitcoin's: the transactions "constitute
the site set of the tangle graph, which is the ledger" — the tangle is the
relation predicated on the transactions that constitute it. -/
def klirToIotaPre : Prefunctor KlirPosition (Paths IotaPosition) where
  obj | .things => .transaction | .relation => .tangle
  map | .relation_on_things => Quiver.Hom.toPath IotaArrow.stores

/-- The kernel embedding functor I_Klir ⥤ I_Iota. Faithfulness is free:
every functor out of I_Klir is faithful (CommonCore §Faithfulness). -/
def klirToIota : Paths KlirPosition ⥤ Paths IotaPosition :=
  Paths.lift klirToIotaPre

theorem klirToIota_obj_injective : Function.Injective klirToIotaPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [klirToIotaPre]

theorem klirToIota_faithful : klirToIota.Faithful :=
  faithful_of_subsingleton_hom _

-- ═══════════════════════════════════════════════════════════════════════════════
-- § The chain signature, doubled: approval ancestry is an infinite hom-set
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The approval-ancestry path of depth n along the first approval slot. -/
def approvalChain : ℕ → Quiver.Path IotaPosition.transaction IotaPosition.transaction
  | 0 => .nil
  | n + 1 => (approvalChain n).cons IotaArrow.approves₁

theorem approvalChain_length (n : ℕ) : (approvalChain n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [approvalChain, Quiver.Path.length_cons, ih]

theorem approvalChain_injective : Function.Injective approvalChain := by
  intro a b h
  have hlen := congrArg Quiver.Path.length h
  rw [approvalChain_length, approvalChain_length] at hlen
  exact hlen

/-- The approval hom-set `transaction ⟶ transaction` is infinite. -/
instance : Infinite (Quiver.Path IotaPosition.transaction IotaPosition.transaction) :=
  Infinite.of_injective approvalChain approvalChain_injective

/-- **No faithful functor I_Iota ⥤ I_Klir exists** — the chain-family
pigeonhole, through the approval loop. -/
theorem iota_no_faithful_functor_to_klir
    (F : IotaShape ⥤ Paths KlirPosition) : ¬ F.Faithful := by
  intro hF
  haveI := hF
  have h01 : F.map (approvalChain 0) = F.map (approvalChain 1) :=
    Subsingleton.elim _ _
  have : approvalChain 0 = approvalChain 1 := F.map_injective h01
  simpa using approvalChain_injective this

/-- The `tangle` hom-set is trivial: nothing targets `tangle`. The
relation-image is thin, exactly as Bitcoin's `coin` — same cell of the
taxonomy. -/
theorem iota_tangle_self
    (p : Quiver.Path IotaPosition.tangle IotaPosition.tangle) : p = .nil := by
  cases p with
  | nil => rfl
  | cons _ e => exact nomatch e

-- ═══════════════════════════════════════════════════════════════════════════════
-- § The branching separation: same cell as Bitcoin, doubled arrows
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Bitcoin's endo-generator at the chained role is UNIQUE: every generating
arrow `transaction → transaction` is `hash_prev`. -/
theorem bitcoin_endo_unique
    (e : BitcoinArrow .transaction .transaction) : e = .hash_prev := by
  cases e
  rfl

/-- IOTA's two approval slots are DISTINCT parallel endo-generators. -/
theorem iota_parallel_approvals :
    IotaArrow.approves₁ ≠ IotaArrow.approves₂ := by
  intro h
  injection h

/-- **The branching separation.** IOTA occupies Bitcoin's history locus —
content-things, with a thin relation-image — but asserts two distinct
parallel endo-generators where Bitcoin asserts exactly one. The DAG/chain
distinction is a branching width WITHIN the chain family, not a fourth
history locus. -/
theorem iota_branching_separation :
    (∃ e₁ e₂ : IotaArrow .transaction .transaction, e₁ ≠ e₂) ∧
    (∀ e : BitcoinArrow .transaction .transaction, e = .hash_prev) :=
  ⟨⟨.approves₁, .approves₂, iota_parallel_approvals⟩, bitcoin_endo_unique⟩
