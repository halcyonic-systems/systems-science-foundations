/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Shape Category for Joslyn's Semantic Control Systems

The *shape category* `I_Joslyn` encodes the dependency structure of Joslyn's
control₂ system definition CS = (C, O_E, O_I) from "Semantic Control Systems"
(*World Futures* 45:87-123, 1995). Defs 25, 28, Prop 29. Zotero key: JXTBBK89.

## Construction

We define a quiver with 3 vertices (the tuple positions) and 3 generating arrows
(the functional relations from Figure 1), then take the free category via `Paths`.

## Arrow Direction Convention

Arrows point in the *functional direction* (same direction as the named function).
This encodes the causal/information flow structure of the control₂ system.

- h: C → O_E (disturbance: environment acts on regulator)
- g: O_E → O_I (efferent: regulator constrains controlled variables)
- f: O_I → O_E (afferent: feedback from controlled variables to regulator)

## Cyclic Structure

The feedback cycle (efferent ∘ afferent and afferent ∘ efferent) distinguishes this
from ALL other shape categories in the landscape. Bunge, Mobus, Myers, and Wymore
all have DAG-shaped quivers (no cycles). Joslyn's cycle encodes the FEEDBACK structure
that is definitional to cybernetic control systems.

In the free category, the cycle between `effector` and `controlled` generates
infinitely many morphisms (paths of alternating efferent and afferent arrows).

## Proposition 29

Joslyn's Proposition 29 establishes that control₂ REQUIRES the internal decomposition
O = (O_E, O_I). The split is not optional but necessary for active feedback control.
This is the cybernetic analog of Mesarović's decomposition theorem.
-/

/-- The three positions in Joslyn's control₂ system definition CS = (C, O_E, O_I).

- `controller`: C — the global environment (source of disturbances; hierarchically superior)
- `effector`: O_E — the external/efferent component (the regulator/effector; active part)
- `controlled`: O_I — the internal/afferent component (controlled variables; stable part)
-/
inductive JoslynPosition
  | controller
  | effector
  | controlled
  deriving DecidableEq, Inhabited

/-- Generating morphisms for the Joslyn shape quiver.

Each arrow encodes a functional relation from Joslyn (1995) Figure 1:
- `disturbance`: h — environmental disturbance acts on the regulator (C → O_E)
- `efferent`: g — regulator constrains controlled variables (O_E → O_I)
- `afferent`: f — feedback from controlled variables to regulator (O_I → O_E)

Note: the `efferent` and `afferent` arrows form a cycle, generating infinitely many
morphisms in the free category. This cyclic structure is unique among the shape
categories in this formalization and encodes the defining feedback loop of cybernetic
control systems.
-/
inductive JoslynArrow : JoslynPosition → JoslynPosition → Type
  | disturbance : JoslynArrow .controller .effector
  | efferent : JoslynArrow .effector .controlled
  | afferent : JoslynArrow .controlled .effector

instance : Quiver JoslynPosition where
  Hom := JoslynArrow

open CategoryTheory in
/-- The shape category for Joslyn's semantic control systems: the free category on the
functional-relation quiver.

Unlike the DAG-shaped quivers of Bunge, Mobus, Myers, and Wymore, this shape category
has a cycle between `effector` and `controlled`. The free category on a cyclic quiver
has infinitely many morphisms between the cyclic vertices — each distinct path of
alternating efferent/afferent arrows is a genuinely different control trajectory.
This infinite morphism structure formally encodes the open-ended nature of feedback. -/
abbrev JoslynShape := Paths JoslynPosition
