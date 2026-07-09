/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic
import Systems.Category.ShapeKlir
import Systems.Category.ShapeMesarovic

/-!
# Shape Category for Willems' Behavioral Triple Σ = (T, W, B)

The *shape category* `I_Willems` encodes the dependency structure of Willems'
behavioral definition of a dynamical system: Σ = (T, W, B) with B ⊆ Wᵀ.

## Sources

- Willems, "The Behavioral Approach to Open and Interconnected Systems,"
  IEEE Control Systems Magazine (2007), pp. 50–51 — the triple, cited verbatim
  from here (Zotero 62DKW5QM).
- Willems, "Paradigms and Puzzles in the Theory of Dynamical Systems,"
  IEEE Trans. Automatic Control 36(3) (1991) — Def II.1 (the triple),
  Def VII.1 and §VII (state models), Def XII.1 (interconnection)
  (Zotero K635IXZM). The 1991 display math is OCR-fragile; where both
  papers state a definition, the 2007 wording is cited.

## Construction

- `time`: T — the time axis
- `signal`: W — the signal space
- `behavior`: B ⊆ Wᵀ — the set of admissible trajectories (the system)

Arrows point in the functional direction (convention of Wymore/Spivak):
a trajectory w ∈ B is a map T → W, so behavior produces signal values and
is indexed by time points.

- `evaluate : behavior → signal` — trajectories assign signal values
  (the predication of B on W: the kernel arrow)
- `indexed_by : behavior → time` — trajectories are indexed by the time axis

Two arrows, not one: T and W are separately named constituents of Willems'
own triple. Fusing Wᵀ into a single position would smuggle the
trajectory-space construction into a position name. Dropping `time` leaves
the walking arrow itself — Willems is the sparsest entry in the landscape,
nearest the bare kernel.

## Layered Status (kernel-neutrality witness, not tradition #9)

Willems enters the landscape as a stress test of kernel neutrality, with a
layered verdict. Each layer is stated in this file's mathematics or named as
out of scope:

- **Kernel layer — embeds.** `klirToWillems` below: the tradition most hostile
  to I/O orientation still carries the predication arrow. `dep_on` is
  predication, not causation.
- **Shape layer — collapses.** `willemsToMesarovic` below: as a shape,
  I_Willems is the span time ← behavior → signal, isomorphic to Mesarović's
  Shape 2 span input ← globalState → output. Willems is therefore NOT counted
  in the eight-traditions headline: a ninth-tradition claim would assert
  independence on the one measure (single-system shape) where Willems provably
  collapses. Spivak's precedent does not transfer — his caveat is sociological
  while his commitment stays shape-visible.
- **Composition layer — independent, not encoded here.** Willems' genuinely
  novel commitments live at the composition layer and are NOT encoded in this
  file: interconnection as behavior intersection B₁ ∩ B₂ (1991 §XII);
  input/output partition as a theorem about a behavior rather than a
  definitional primitive (2007 p. 55); latent-variable elimination
  (1991 Thm IV.3; 2007 pp. 53, 57). Tracked as SSF #16
  (category-of-behaviors layer).

## The Semantics of the Collapse (why the iso is the finding)

The shape iso is forced to send `time ↦ input` and `behavior ↦ globalState`.
Both assignments are semantic nonsense. Willems has no state object: the
behavioral point is that state is a latent variable of a *representation*
(1991 Def VII.1; p. 269 "state-space representation"; p. 290), the independent
echo of the state-as-role reading — compare `SpivakSystem.lean`'s
`dep ↦ parameter` casting docstring. And Willems' time axis is nobody's input.
The absurdity of the iso's semantics is the demonstration that the collapse is
a shape-level artifact: the abstraction discards exactly what Willems means.
This is the "entries are claims-at-a-layer" finding rendered as mathematics —
the shape functor cannot see the difference between a passive state projection
and a trajectory evaluation, so identity of shape cannot certify identity
of commitment.
-/

open CategoryTheory

/-- The three positions in Willems' behavioral triple Σ = (T, W, B)
(1991 Def II.1; the triple cited from 2007 pp. 50–51 due to 1991 OCR).

- `time`: T — the time axis
- `signal`: W — the signal space
- `behavior`: B ⊆ Wᵀ — the set of admissible trajectories (the system)
-/
inductive WillemsPosition
  | time
  | signal
  | behavior
  deriving DecidableEq, Inhabited

/-- Generating morphisms for the Willems shape quiver, in the functional
direction (convention of Wymore/Spivak): a trajectory w ∈ B is a map T → W,
so behavior produces signal values and consumes time points.

- `evaluate`: behavior → signal — trajectories assign signal values
  (the predication of B on W: the kernel arrow)
- `indexed_by`: behavior → time — trajectories are indexed by the time axis
-/
inductive WillemsArrow : WillemsPosition → WillemsPosition → Type
  | evaluate   : WillemsArrow .behavior .signal
  | indexed_by : WillemsArrow .behavior .time

instance : Quiver WillemsPosition where
  Hom := WillemsArrow

/-- The shape category for Willems' behavioral triple: the free category on the
trajectory quiver.

3 objects, 2 arrows radiating outward from `behavior` — the span
time ← behavior → signal. No composable chains exist (behavior is the only
source; time and signal are sinks). Dropping `time` leaves the walking arrow:
Willems is the sparsest entry in the landscape, nearest the bare kernel. -/
abbrev WillemsShape := Paths WillemsPosition

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Kernel embedding: I_Klir → I_Willems (the neutrality theorem)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Embedding I_Klir into I_Willems: things ↦ signal, relation ↦ behavior,
relation_on_things ↦ evaluate.

The tradition most hostile to I/O orientation still carries the predication
arrow — a behavior is a relation predicated on signal values. `dep_on` is
predication, not causation, so the behavioral stance has nothing to refuse. -/
def klirToWillemsPre : Prefunctor KlirPosition (Paths WillemsPosition) where
  obj | .things => .signal | .relation => .behavior
  map | .relation_on_things => Quiver.Hom.toPath WillemsArrow.evaluate

/-- The kernel embedding functor I_Klir ⥤ I_Willems. Faithfulness is free:
every functor out of I_Klir is faithful (CommonCore §Faithfulness). -/
def klirToWillems : Paths KlirPosition ⥤ Paths WillemsPosition :=
  Paths.lift klirToWillemsPre

theorem klirToWillems_obj_injective : Function.Injective klirToWillemsPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [klirToWillemsPre]

-- ═══════════════════════════════════════════════════════════════════════════════
-- § The collapse, stated in the math: I_Willems ≅ I_Mesarovic as shapes
--
-- Pattern: ShapeComparison_Wymore.lean; precedent for stating proximity in
-- Lean rather than prose: myersToSpivak. Minimum bar per the ratified verdict:
-- both-direction functors + object bijection + arrow-correspondence theorems.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Object-level comparison: Willems' span projected onto Mesarović's Shape 2 span.

The assignments `behavior ↦ globalState` and `time ↦ input` are forced by the
shapes and are semantically absurd — see the module docstring. The absurdity is
the finding. -/
def willemsToMesarovicObj : WillemsPosition → MesarovicPosition
  | .behavior => .globalState
  | .signal   => .output
  | .time     => .input

/-- The forward comparison as a prefunctor into the Mesarović path category.
Both generating arrows map to generating arrows: the spans match leg for leg. -/
def willemsToMesarovicPre : Prefunctor WillemsPosition (Paths MesarovicPosition) where
  obj := willemsToMesarovicObj
  map
    | .evaluate   => Quiver.Hom.toPath MesarovicArrow.response_output
    | .indexed_by => Quiver.Hom.toPath MesarovicArrow.response_input

/-- The forward comparison functor I_Willems ⥤ I_Mesarovic. -/
def willemsToMesarovic : Paths WillemsPosition ⥤ Paths MesarovicPosition :=
  Paths.lift willemsToMesarovicPre

/-- Object-level inverse: Mesarović's span read back into Willems' span. -/
def mesarovicToWillemsObj : MesarovicPosition → WillemsPosition
  | .globalState => .behavior
  | .output      => .signal
  | .input       => .time

/-- The reverse comparison as a prefunctor into the Willems path category. -/
def mesarovicToWillemsPre : Prefunctor MesarovicPosition (Paths WillemsPosition) where
  obj := mesarovicToWillemsObj
  map
    | .response_output => Quiver.Hom.toPath WillemsArrow.evaluate
    | .response_input  => Quiver.Hom.toPath WillemsArrow.indexed_by

/-- The reverse comparison functor I_Mesarovic ⥤ I_Willems. -/
def mesarovicToWillems : Paths MesarovicPosition ⥤ Paths WillemsPosition :=
  Paths.lift mesarovicToWillemsPre

-- § Object bijection

theorem willemsToMesarovicObj_bijective : Function.Bijective willemsToMesarovicObj := by
  constructor
  · intro a b h; cases a <;> cases b <;> simp_all [willemsToMesarovicObj]
  · intro m
    cases m with
    | input       => exact ⟨.time, rfl⟩
    | output      => exact ⟨.signal, rfl⟩
    | globalState => exact ⟨.behavior, rfl⟩

/-- The object maps are mutually inverse (Willems side). -/
theorem willems_mesarovic_obj_left_inverse (p : WillemsPosition) :
    mesarovicToWillemsObj (willemsToMesarovicObj p) = p := by
  cases p <;> rfl

/-- The object maps are mutually inverse (Mesarović side). -/
theorem willems_mesarovic_obj_right_inverse (m : MesarovicPosition) :
    willemsToMesarovicObj (mesarovicToWillemsObj m) = m := by
  cases m <;> rfl

-- § Arrow correspondence: every generating arrow maps to a generating arrow
--   (length-1 paths in both directions — no mediation, unlike Wymore → Mobus)

theorem willems_evaluate_length :
    (willemsToMesarovicPre.map WillemsArrow.evaluate).length = 1 := rfl

theorem willems_indexed_by_length :
    (willemsToMesarovicPre.map WillemsArrow.indexed_by).length = 1 := rfl

theorem mesarovic_response_output_length :
    (mesarovicToWillemsPre.map MesarovicArrow.response_output).length = 1 := rfl

theorem mesarovic_response_input_length :
    (mesarovicToWillemsPre.map MesarovicArrow.response_input).length = 1 := rfl
