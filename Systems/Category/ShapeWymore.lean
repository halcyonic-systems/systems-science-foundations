/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Shape Category for Wymore's FSD (Full System Description)

The *shape category* `I_Wymore` encodes the dependency structure of Wymore's
Full System Description FSD = (Z, DS_Z, TS_Z) where the core system model is
the quintuple Z = (S_Z, I_Z, O_Z, N_Z, R_Z):
- S_Z = state set
- I_Z = input set
- O_Z = output set
- N_Z = next-state function (S × I → S)
- R_Z = readout function (S → O, Moore-type)

Source: Wach et al. (2021) "Conjoining Wymore's Systems Theoretic Framework and
the DEVS Modeling Formalism," Appendix B Eq. A1, citing Wymore (1993) *T3SD*.
Zotero key: BNPE2684.

## Construction

4 objects (`state`, `input`, `output`, `time`) and 3 generating arrows
(`nextState`, `readout`, `stateOnTime`). All arrows radiate outward from `state`,
following the functional direction convention established in `ShapeMyers`.

## Arrow Direction Convention

Same as Myers/Bunge/Mobus: arrows follow the *functional* direction.
- `nextState : state → input` — N_Z has type S × I → S; input is consumed
- `readout : state → output` — R_Z has type S → O; state produces output
- `stateOnTime : state → time` — state transitions are indexed by timescale

## Relationship to Myers

At the quintuple (Z) level without time, this shape is structurally IDENTICAL to
Myers's shape category: both have 3 objects (state, input, output) with 2 arrows
radiating from state (one to input, one to output). This confirms that Myers's
deterministic system definition is exactly Wymore's core state machine Z without
explicit time. The FSD-level `time` object is Wymore's distinctive addition,
reflecting his engineering emphasis on discrete simulation timescales.

## Relationship to Mobus

Wymore's FSD includes an explicit timescale (TS_Z), paralleling Mobus's `Δt`.
The comparison functor `I_Wymore → I_Mobus` maps `time ↦ timeScale` and
`state ↦ components`, collapsing Wymore's single-component view into Mobus's
multi-component framework.
-/

/-- The four positions in Wymore's Full System Description (FSD level).

- `state`: S_Z — the set of internal states
- `input`: I_Z — the set of inputs (stimuli from environment)
- `output`: O_Z — the set of outputs (readout values)
- `time`: TS_Z — the discrete timescale for state transitions
-/
inductive WymorePosition
  | state
  | input
  | output
  | time
  deriving DecidableEq, Inhabited

/-- Generating morphisms for the Wymore shape quiver.

Each arrow encodes a functional dependency from the FSD definition:
- `nextState`: N_Z : S × I → S (state depends on input for transitions)
- `readout`: R_Z : S → O (output is produced from state, Moore-type)
- `stateOnTime`: state transitions are parameterized by TS_Z

These correspond to the two functions in the quintuple Z plus the FSD time-indexing:
- `N_Z : S_Z × I_Z → S_Z` (next-state)
- `R_Z : S_Z → O_Z` (readout)
- FSD temporal parameterization via TS_Z
-/
inductive WymoreArrow : WymorePosition → WymorePosition → Type
  | nextState : WymoreArrow .state .input
  | readout : WymoreArrow .state .output
  | stateOnTime : WymoreArrow .state .time

instance : Quiver WymorePosition where
  Hom := WymoreArrow

open CategoryTheory in
/-- The shape category for Wymore's FSD: the free category on the system quiver.

State is the sole source; input, output, and time are sinks. Every non-identity
morphism is a generating arrow — no composite paths exist (same as Myers).

Without the `time` vertex, this is isomorphic to `MyersShape`, confirming that
Myers's lens-based deterministic system is Wymore's quintuple Z with the temporal
dimension abstracted away. The FSD time object is what distinguishes Wymore's
engineering-oriented framework from Myers's categorical one. -/
abbrev WymoreShape := Paths WymorePosition
