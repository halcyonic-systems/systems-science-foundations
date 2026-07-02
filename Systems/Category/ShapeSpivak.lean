/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic
import Systems.Category.ShapeMyers

/-!
# Shape Category for Spivak's Adaptive Arrangements

The *shape category* `I_Spivak` encodes the dependency structure of Spivak's
definition of system as a 0-ary morphism in the operad Arr_Sm of smooth adaptive
arrangements ("Compositional Dynamics in Learning and Mechanics,"
arXiv:2606.28984, Defs 5.3.1–5.3.2, Remark 4.1.2, June 2026).

## Construction

A 0-ary arrangement φ: I → c carries the data (Q, ♯_Q, f⁺, f⁻, U):
- Q — the reactive parameter space (internal state, with reaction ♯_Q)
- f⁺: Q → N⁺ — the output map
- f⁻: Q × N⁻ → 1 — the input map (backward pass)
- U: Q × N⁻ → ℝ — the potential

4 objects (`parameter`, `output`, `input`, `potential`) and 5 generating arrows.
The shape category captures the positional structure without the operad/Poly
machinery, exactly as `I_Myers` abstracts the lens machinery.

## Arrow Direction Convention

Arrows point in the *functional direction* (same as Joslyn): each arrow follows
a named function or reaction. Under this convention `expose` and `update` read
exactly as Myers wrote them.

- `expose : parameter → output` — f⁺ reads the parameter to produce output
- `update : parameter → input` — the backward pass consumes input
- `potential_on_parameter : potential → parameter` — U reads Q
- `potential_on_input : potential → input` — U reads N⁻
- `drive : parameter → potential` — the reaction ♯ turns dU into a parameter step

## Cyclic Structure

`drive` and `potential_on_parameter` form a cycle parameter ⇄ potential — the
second cyclic shape in the landscape (precedent: `ShapeJoslyn.lean`). The two
cycles encode different commitments: Joslyn's cycle is feedback through
*observation* (efferent/afferent), Spivak's is feedback through *value* — the
state changes because a potential evaluates it. That is the new commitment this
tradition adds to the convergence table: potential + reaction, value-driven
adaptation. No other tradition in the landscape formalizes *why* state moves.

## Relationship to Myers

`I_Myers` sits inside `I_Spivak` literally: state ↦ parameter, output ↦ output,
input ↦ input, with expose ↦ expose and update ↦ update. The inclusion
`myersToSpivak` below makes the commitments ladder of Remark 4.1.2 a theorem —
Spivak = Myers + potential + drive.

## Independence Caveat

Spivak and Myers share the Topos-adjacent community and the lens machinery
(Myers appears in the paper's acknowledgments). The commitment is new, but the
sociological independence of this convergence entry is weaker than, say,
Klir-vs-Mobus. The `myersToSpivak` inclusion states the shared-machinery
relationship in the mathematics rather than hiding it.
-/

/-- The four positions in Spivak's 0-ary adaptive arrangement (Q, ♯_Q, f⁺, f⁻, U).

- `parameter`: Q — the reactive parameter space (internal state with reaction ♯_Q)
- `output`: N⁺ — the output space of the interface
- `input`: N⁻ — the input space of the interface
- `potential`: ℝ — the value object the potential U maps into
-/
inductive SpivakPosition
  | parameter
  | output
  | input
  | potential
  deriving DecidableEq, Inhabited

/-- Generating morphisms for the Spivak shape quiver.

- `expose`: f⁺ reads the parameter to produce output (identical to Myers's expose)
- `update`: the backward pass consumes input (identical to Myers's update)
- `potential_on_parameter`: the potential U reads Q
- `potential_on_input`: the potential U reads N⁻
- `drive`: the reaction ♯ turns dU into a parameter step — the new commitment

`drive` and `potential_on_parameter` form the value-feedback cycle
parameter ⇄ potential.
-/
inductive SpivakArrow : SpivakPosition → SpivakPosition → Type
  | expose : SpivakArrow .parameter .output
  | update : SpivakArrow .parameter .input
  | potential_on_parameter : SpivakArrow .potential .parameter
  | potential_on_input : SpivakArrow .potential .input
  | drive : SpivakArrow .parameter .potential

instance : Quiver SpivakPosition where
  Hom := SpivakArrow

open CategoryTheory in
/-- The shape category for Spivak's adaptive arrangements: the free category on
the arrangement quiver.

Like `I_Joslyn`, this shape has a cycle — here between `parameter` and
`potential` — so the free category has infinitely many morphisms between the
cyclic vertices. Each distinct path of alternating drive/potential arrows is a
genuinely different adaptation trajectory: evaluate, step, re-evaluate. Where
Joslyn's cycle encodes feedback through observation, this one encodes feedback
through value. -/
abbrev SpivakShape := Paths SpivakPosition

open CategoryTheory

-- ═══════════════════════════════════════════════════════════════════════════════
-- § The commitments ladder: I_Myers includes into I_Spivak
--
-- Remark 4.1.2 presents the framework as a ladder where each stage adds exactly
-- one commitment. At the shape level: Spivak's positions and arrows contain
-- Myers's verbatim, plus `potential` and the three potential/drive arrows.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The inclusion of Myers's lens shape into the Spivak shape:
state ↦ parameter, output ↦ output, input ↦ input. Both generating arrows
map to their namesakes. -/
def myersToSpivakPre : Prefunctor MyersPosition (Paths SpivakPosition) where
  obj | .state => .parameter | .output => .output | .input => .input
  map
    | .expose => Quiver.Hom.toPath SpivakArrow.expose
    | .update => Quiver.Hom.toPath SpivakArrow.update

/-- The inclusion functor I_Myers → I_Spivak: the commitments ladder of
Remark 4.1.2 as a theorem. Spivak = Myers + potential + drive. -/
def myersToSpivak : Paths MyersPosition ⥤ Paths SpivakPosition :=
  Paths.lift myersToSpivakPre

theorem myersToSpivak_obj_injective : Function.Injective myersToSpivakPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [myersToSpivakPre]
