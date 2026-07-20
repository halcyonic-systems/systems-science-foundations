/-
  Systems/Klir/Gates.lean
  The lens-entry gate booleans, shared by every binding rung (bert-lenses#24).

  These are the computable Boolean forms of the two `ViewGeneration.lean`
  preconditions, plus the mapping from a pair of gate verdicts to the four
  mode-entry rights they license. They live in their own `main`-free module so
  that both the fixture enumerator (`GatesTruthTable.lean`, Rung 1) and the
  subprocess oracle (`GatesOracle.lean`, Rung 1.5) call the SAME declarations —
  a Rust gate can then only drift from ONE Lean source of truth, whichever rung
  catches it.

  The gates are polymorphic over any `DecidableEq` relatum type: enumeration
  instantiates them at `Fin n`, the oracle at `ℕ` on stdin-parsed models. They
  read only pairwise (in)equality, so both instantiations compute the identical
  logic. The anchoring to the actual `Kernel.HasBond` / `Kernel.Irreflexive`
  predicates is proved in `GatesTruthTable.lean` (`hasBondB_iff` /
  `irreflexiveB_iff`) against the total-action pinning.
-/

namespace Systems.GatesTruthTable

universe u

/-! ## The gate booleans -/

/-- Structural gate: the dependency contains a distinct pair. Under the total
    action pinning this is exactly `Kernel.HasBond` (see `hasBondB_iff`). -/
def hasBondB {α : Type u} [DecidableEq α] (D : List (α × α)) : Bool :=
  D.any fun p => decide (p.1 ≠ p.2)

/-- Operational gate: no pair depends on itself. Exactly `Kernel.Irreflexive`
    (see `irreflexiveB_iff`). -/
def irreflexiveB {α : Type u} [DecidableEq α] (D : List (α × α)) : Bool :=
  D.all fun p => decide (p.1 ≠ p.2)

/-! ## Mode mapping

  The four mode-entry verdicts a pair of gate booleans licenses. Shared by the
  fixture emitter (`rowJson`) and the oracle (`GatesOracle.lean`) so the two
  never disagree on how the gates translate to lens-entry rights. -/

/-- Mode-entry rights: `core` is free (on-ness holds by construction), the two
    gates are `structural`/`operational`, and `full` extends `operational` (its
    extra dynamical-face check only warns, so it never blocks entry). -/
structure ModeVerdicts where
  core : Bool
  structural : Bool
  operational : Bool
  full : Bool

/-- Translate the two gate booleans into the four mode verdicts. -/
def modesOf (hasBond irreflexive : Bool) : ModeVerdicts :=
  { core := true
    structural := hasBond
    operational := irreflexive
    full := irreflexive }

end Systems.GatesTruthTable
