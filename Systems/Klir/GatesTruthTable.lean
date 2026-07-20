/-
  Systems/Klir/GatesTruthTable.lean
  Rung 1 of the lens-entry binding (bert-lenses#24)

  Enumerate every small (T, R) kernel and evaluate the named lens-entry
  preconditions on each, emitting a fixture the Rust gate functions are tested
  against in CI. Until this file exists the mode stamp is decorative relative to
  the proof object: the Rust gates are hand-mirrored from Lean-named
  preconditions with no chain of custody. This is the falsifiability floor — a
  Rust gate that drifts from a Lean precondition turns CI red on a committed
  row.

  The two preconditions this binds are exactly the two ViewGeneration.lean
  charges for a lens:
  - `Kernel.HasBond`     — the Bunge (Structural) view's cost: a bonded pair of
                           distinct relata.
  - `Kernel.Irreflexive` — the Mobus (Operational/Full) view's cost: no
                           self-dependency (§4.3, k ≠ o).
  The Klir (Core) view is free — on-ness is the only charge and it holds by
  construction here (`dep ⊆ things × things`, with `things = univ`).

  ACTSON PINNING. `Kernel.HasBond` is semantic: it needs `Bonded`, hence an
  `ActsOn` instance. The Rust `check_bond` is syntactic — any interaction
  between two distinct systems counts (pinned in `bert-core::transition`'s
  correspondence table). The two agree exactly under the total action instance,
  where every distinct pair is bonded, so `HasBond` collapses to "the dependency
  contains a distinct pair". That instance is what these rows are computed
  against; `hasBondB_iff` proves the collapse rather than asserting it.

  The gate booleans are anchored to the real ViewGeneration predicates by
  `hasBondB_iff` / `irreflexiveB_iff` — the enumeration reports the predicates
  the proofs are about, not a re-implementation that happens to agree.

  Regenerate the fixture with (from the SSF repo root):
    lake env lean --run Systems/Klir/GatesTruthTable.lean \
      > ../bert-lenses/fixtures/gates_truth_table.json
-/

import Systems.Klir.ViewGeneration

namespace Systems.GatesTruthTable

open Systems

/-! ## Small kernels over `Fin n`

  A small model fixes `things = univ` over `Fin n` and varies the dependency `R`
  over every subset of `Fin n × Fin n`, carried as a duplicate-free list. Fixing
  `things` keeps `dep_on` trivial; the gates read only `dep`, so this loses no
  gate-relevant variation. -/

/-- The kernel on `Fin n` whose dependency is the pairs in `D` (things are all of
    `Fin n`, so the arrow constraint is immediate). -/
def kernelOf {n : ℕ} (D : List (Fin n × Fin n)) : Kernel (Fin n) where
  things := Set.univ
  dep := {p | p ∈ D}
  dep_on := fun p _ => ⟨Set.mem_univ p.1, Set.mem_univ p.2⟩

/-- Every ordered pair of relata, in a fixed (row-major) order. -/
def allPairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i => (List.finRange n).map fun j => (i, j)

/-- Every sublist of `l`, deterministically ordered — the powerlist. -/
def powerlist {α : Type*} : List α → List (List α)
  | [] => [[]]
  | a :: rest => let s := powerlist rest; s.map (a :: ·) ++ s

/-- Every dependency `R ⊆ Fin n × Fin n`, deterministically ordered so the
    emitted fixture is byte-stable across regenerations. -/
def subsets (n : ℕ) : List (List (Fin n × Fin n)) :=
  powerlist (allPairs n)

/-! ## The gate booleans

  Computable Boolean forms of the two ViewGeneration preconditions, evaluated
  during enumeration. -/

/-- Structural gate: the dependency contains a distinct pair. Under the total
    action pinning this is exactly `Kernel.HasBond` (see `hasBondB_iff`). -/
def hasBondB {n : ℕ} (D : List (Fin n × Fin n)) : Bool :=
  D.any fun p => decide (p.1 ≠ p.2)

/-- Operational gate: no pair depends on itself. Exactly `Kernel.Irreflexive`
    (see `irreflexiveB_iff`). -/
def irreflexiveB {n : ℕ} (D : List (Fin n × Fin n)) : Bool :=
  D.all fun p => decide (p.1 ≠ p.2)

/-! ## Chain of custody

  The gate booleans decide the actual ViewGeneration predicates, under the total
  action instance for the bond charge. -/

/-- The total action instance: every thing acts on every thing, so `Bonded`
    holds for every pair. This is the semantics `check_bond` computes. -/
local instance totalActsOn (n : ℕ) : ActsOn (Fin n) := ⟨fun _ _ => True⟩

theorem irreflexiveB_iff {n : ℕ} (D : List (Fin n × Fin n)) :
    irreflexiveB D = true ↔ (kernelOf D).Irreflexive := by
  simp [irreflexiveB, Kernel.Irreflexive, kernelOf, List.all_eq_true]

theorem hasBondB_iff {n : ℕ} (D : List (Fin n × Fin n)) :
    hasBondB D = true ↔ (kernelOf D).HasBond := by
  simp only [hasBondB, Kernel.HasBond, kernelOf, List.any_eq_true,
    Set.mem_setOf_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨p, hp, hne⟩
    exact ⟨p, hp, hne, Or.inl trivial⟩
  · rintro ⟨p, hp, hne, _⟩
    exact ⟨p, hp, hne⟩

/-! ## Fixture emission -/

def boolJson (b : Bool) : String := if b then "true" else "false"

/-- One row: the model, the two gate verdicts, and the four mode-entry verdicts
    they license. `core` is free; `structural`/`operational` are the two gates;
    `full` extends `operational` (its extra dynamical-face check only warns, so
    it never blocks entry). -/
def rowJson {n : ℕ} (D : List (Fin n × Fin n)) : String :=
  let dep := String.intercalate ", "
    (D.map fun p => "[" ++ toString p.1.val ++ ", " ++ toString p.2.val ++ "]")
  let things := String.intercalate ", "
    ((List.finRange n).map fun i => toString i.val)
  let hb := boolJson (hasBondB D)
  let irr := boolJson (irreflexiveB D)
  String.intercalate "" [
    "{\"n\": ", toString n,
    ", \"things\": [", things,
    "], \"dep\": [", dep,
    "], \"gates\": {\"has_bond\": ", hb, ", \"irreflexive\": ", irr,
    "}, \"modes\": {\"core\": true, \"structural\": ", hb,
    ", \"operational\": ", irr, ", \"full\": ", irr, "}}"
  ]

/-- Every row, small `n` first, dependency subsets in `subsets` order. The bound
    `n ≤ 2` fully enumerates every boundary case (empty, self-loop-only, one
    distinct edge, and their combinations) while keeping the fixture reviewable. -/
def allRows : List String :=
  (subsets 0).map rowJson ++ (subsets 1).map rowJson ++ (subsets 2).map rowJson

/-- The fixture: a generator-provenance header plus the enumerated rows. -/
def fixtureJson : String :=
  let rows := String.intercalate ",\n    " allRows
  String.intercalate "" [
    "{\n",
    "  \"_generator\": {\n",
    "    \"source\": \"systems-science-foundations/Systems/Klir/GatesTruthTable.lean\",\n",
    "    \"command\": \"lake env lean --run Systems/Klir/GatesTruthTable.lean > ../bert-lenses/fixtures/gates_truth_table.json\",\n",
    "    \"lean_decls\": {\"has_bond\": \"Systems.Kernel.HasBond\", \"irreflexive\": \"Systems.Kernel.Irreflexive\", \"klir_view\": \"Systems.Kernel.toKlir\"},\n",
    "    \"acts_on_pinning\": \"HasBond is computed under the total action instance, where every distinct pair is bonded; this is the syntactic semantics bert-core::check_bond implements. See hasBondB_iff.\",\n",
    "    \"bound\": \"all (T, R) kernels over Fin n for n <= 2, with T = univ\",\n",
    "    \"row_count\": ", toString allRows.length, "\n",
    "  },\n",
    "  \"rows\": [\n    ", rows, "\n  ]\n",
    "}"
  ]

def emit : IO Unit := IO.println fixtureJson

end Systems.GatesTruthTable

/-- Entry point for `lake env lean --run`: print the fixture to stdout. -/
def main : IO Unit := Systems.GatesTruthTable.emit
