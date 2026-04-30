/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Shape Categories for Mesarović & Takahara's General Systems Theory

Two shape categories encoding Mesarović & Takahara (1975) *General Systems Theory:
Mathematical Foundations*, Ch. II Defs 1.1–1.4.

## Source

Mesarović & Takahara (1975), Ch. II:
- Def 1.1: S ⊆ ×{Vᵢ : i ∈ I} (general system as relation on abstract sets)
- Def 1.2: S ⊂ V × Y (I/O partition: V = input object, Y = output object)
- Def 1.4: Given S, there exists a global state set C and response function R : C → V × Y

Zotero key: ZA3E2PD3, verified via OCR 2026-04-20.

## Shape 1: `I_Mesarovic_IO` (Def 1.2 — pure I/O system)

2 objects (`input`, `output`) and NO generating arrows. The I/O relation S ⊂ V × Y is
a relation BETWEEN V and Y, not a functional dependency from one to the other. The system
IS the relation — it does not create a directed dependency.

This gives a DISCRETE category (only identity morphisms). This is the most faithful
encoding of Mesarović's extensional stance: the system is identified with its I/O behavior,
with no internal structure imposed.

## Shape 2: `I_Mesarovic` (Def 1.4 — canonical extension with global state)

3 objects (`input`, `output`, `globalState`) and 2 generating arrows:
- `response_input : globalState → input` — R : C → V × Y projected onto V (π₁ ∘ R)
- `response_output : globalState → output` — R : C → V × Y projected onto Y (π₂ ∘ R)

Arrow direction: functional (same as Myers/Wymore). R IS a function C → V × Y. For each
state c ∈ C, R(c) = (v, y) ∈ S determines a specific input-output pair. The two
projections give well-defined maps C → V and C → Y.

## Structural Relationship to Myers

This gives the same outward-radiating-from-state pattern as Myers and Wymore. The
structural identity between Mesarović's {C, V, Y, R} and Myers's {State, In, Out,
expose, update} is NOT coincidental — Myers's definition is the categorification of
Mesarović's I/O + state framework, with the lens structure making R bidirectional.

Key difference from Myers: Mesarović has ONE response function R (read-only: state
determines I/O pair) while Myers has TWO (expose: read, update: write). Mesarović's
system is PASSIVE (no dynamics); Myers adds DYNAMICS via update.

Directionality comparison:
- Both have arrows pointing outward from state
- Myers's `state → input` means "update consumes input" (dynamics)
- Mesarović's `globalState → input` means "state determines which inputs are consistent"
  (constraint/projection)
- Myers's `state → output` means "expose produces output" (dynamics)
- Mesarović's `globalState → output` means "state determines output" (projection)

In short: `I_Mesarovic` is `I_Myers` without the `update` arrow's dynamic interpretation —
it is Myers's shape with passive/constraint semantics only.
-/

-- ============================================================
-- Shape 1: Mesarović I/O System (Def 1.2)
-- ============================================================

/-- The two positions in Mesarović's I/O system definition S ⊂ V × Y.

- `input`: V — the input object (abstract set of input values)
- `output`: Y — the output object (abstract set of output values)
-/
inductive MesarovicIOPosition
  | input
  | output
  deriving DecidableEq, Inhabited

/-- Generating morphisms for the Mesarović I/O shape quiver: EMPTY.

The system S ⊂ V × Y is a relation between V and Y, not a functional dependency.
There are no generating arrows — the quiver is discrete. -/
inductive MesarovicIOArrow : MesarovicIOPosition → MesarovicIOPosition → Type

instance : Quiver MesarovicIOPosition where
  Hom := MesarovicIOArrow

open CategoryTheory in
/-- The shape category for Mesarović's I/O system (Def 1.2): the free category on a
discrete quiver (no generating arrows).

This is a discrete category — the only morphisms are identities. This faithfully
encodes Mesarović's extensional stance: the system IS identified with its I/O
behavior (the relation S), with no internal structure and no directed dependency
between input and output objects. -/
abbrev MesarovicIOShape := Paths MesarovicIOPosition

-- ============================================================
-- Shape 2: Mesarović System with Global State (Def 1.4)
-- ============================================================

/-- The three positions in Mesarović's canonical system with global state.

- `input`: V — the input object
- `output`: Y — the output object
- `globalState`: C — the global state set (Def 1.4: "there exists a set C...")

The response function R : C → V × Y determines how state constrains I/O behavior.
-/
inductive MesarovicPosition
  | input
  | output
  | globalState
  deriving DecidableEq, Inhabited

/-- Generating morphisms for the Mesarović global-state shape quiver.

Both arrows are projections of the response function R : C → V × Y:
- `response_input`: π₁ ∘ R : C → V (state determines the input component)
- `response_output`: π₂ ∘ R : C → Y (state determines the output component)

For each state c ∈ C, R(c) = (v, y) ∈ S specifies a consistent I/O pair. This is a
PASSIVE characterization: "what I/O behavior does this state produce?" There is no
dynamics — no arrow updates state from input. -/
inductive MesarovicArrow : MesarovicPosition → MesarovicPosition → Type
  | response_input : MesarovicArrow .globalState .input
  | response_output : MesarovicArrow .globalState .output

instance : Quiver MesarovicPosition where
  Hom := MesarovicArrow

open CategoryTheory in
/-- The shape category for Mesarović's system with global state (Def 1.4): the free
category on the response-projection quiver.

3 objects, 2 arrows radiating outward from `globalState`. No composable chains exist
(globalState is the only source; input and output are sinks). The shape is isomorphic
to Myers's shape — both are the "span" category `• ← • → •` — but the interpretation
differs: Mesarović's arrows are passive projections (R determines I/O), while Myers's
include dynamic update. -/
abbrev MesarovicShape := Paths MesarovicPosition
