/-
  ProofSketch.lean — Template for LLM-assisted proof targets

  This file is a TEMPLATE, not compilable code. Copy the structure below
  into the appropriate Systems/Core/*.lean file when setting up a new
  proof target.

  Workflow adapted from:
    Tsoukalas et al., "Advancing Mathematics Research with AI-Driven Formal Proof Search,"
    arXiv:2605.22763v1, Google DeepMind, May 2026

  Usage: "Use lean-formalize to prove [theorem]" or
         "Use lean-formalize to attack [sorry target]"
-/

-- ============================================================
-- PROOF SKETCH TEMPLATE
-- Copy everything below into the target .lean file
-- ============================================================

/- PROOF TARGET: [One plain-English sentence stating the theorem]

   MATHEMATICAL INTENT:
   [2-3 sentences: what this theorem says, why it matters for the
    systems ontology, which Mobus principle it serves]

   AVAILABLE TOOLS:
   [List specific definitions and lemmas from the codebase, e.g.:
    - `ConcreteSystem` from Systems/Core/System.lean
    - `NearDecomposable` from Systems/Core/Governance.lean
    - `composition_closure` theorem from Systemness.lean]

   DOES NOT COUNT:
   [Pre-register the near-misses that would look like success but aren't.
    Written BEFORE proving starts, while it is still unknown which route is hard.
    Prune this list to what is actually tempting for this target:
    - the statement specialized to one structure instead of quantified over all
    - an added hypothesis that closes the goal by assuming part of the claim
    - decide / native_decide on a finite instance
    - a new axiom introduced to bridge the gap
    - `def A := B` where A was meant as an independent construction
    - reduction to a lemma of the same strength as the target]

   STRATEGY HINT:
   [Suggested proof approach if known, e.g.:
    "Induction on RecursiveSystem depth, using closure_under_decomposition
     at the inductive step."
    If unknown: "Open — explore structural induction vs direct construction"]
-/

-- theorem target_name :
--     [formal Lean 4 statement] := by
--   sorry

-- ============================================================
-- ATTEMPT LOG TEMPLATE
-- Add below the theorem when an attempt stalls (3+ failed iterations)
-- Remove after the theorem is proved
-- ============================================================

/- ATTEMPT LOG (YYYY-MM-DD)
   Route: [the mathematical idea, not the tactic text]
   Status: LIVE | BLOCKED — [BLOCKED means this route now rests on a missing lemma
           of the same strength as the target. Reopen only on a materially new
           mechanism, invariant, or construction.]
   Strategy: [what was tried]
   Result: [specific compiler error or stuck point]
   Insight: [what was learned about the proof structure]
   Next: [suggested alternative for next session]
-/
