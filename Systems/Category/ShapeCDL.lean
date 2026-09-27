/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Systems.Category.SharedPrimitive

/-!
# Shape Category for a Parametric Map (Categorical Deep Learning)

The *shape category* `I_CDL` encodes one 1-cell of the 2-category `Para` used by
Gavranović, Lessard, Dudzik, von Glehn, Araújo and Veličković, "Position:
Categorical Deep Learning is an Algebraic Theory of All Architectures" (ICML 2024,
arXiv:2402.15332). A 1-cell `A → B` is a pair `(P, f)` with `f : P × A → B`: a
layer with its weights drawn as an explicit input.

## Construction

- `parameter`: P, the weights
- `input`: A
- `output`: B
- `apply_parameter : parameter → output`, `apply_input : input → output`

## Arrow Direction Convention

Functional, as in `ShapeMyers`, `ShapeSpivak` and `ShapeJoslyn`: each arrow follows
the named function `f`. Under the dependency convention of `ShapeKlir` and
`ShapeBunge` both arrows reverse, and the cell becomes a fork instead of a cofork.
Every result below is stated for the functional reading only.

## Status

Not a ninth tradition and not counted in the `CommonCore` headline. `I_CDL` is a
test shape from machine learning, used to ask one question of `SharedPrimitive`:
can a learning architecture play the forcing role that Joslyn plays there?

## Result

The Klir arrow embeds at the quiver level (`klirToCDLQuiver`), as it must: any shape
with an edge between distinct vertices admits it, so this carries no information.

The informative fact is that the untied cell has out-degree at most one
(`cdl_out_degree_le_one`), so it kills the fork exactly as Joslyn does. Willems kills
the cofork and the two-chain. Hence `connected_is_single_arrow_cdl`: a connected
quiver embedding into `I_CDL` and `I_Willems` is a single arrow, with Joslyn not
used. The cybernetic shape and the parametric-map shape are interchangeable for
this purpose.

## Honest limits

The result is relative to the presentation, as `SharedPrimitive` is. It holds for
one cell with its own weights. Weight tying, the mechanism behind CDL's equivariance
constraints, sends one parameter vertex to two cells, which is a fork
(`tied_has_fork`), and the tied shape cannot stand in for Joslyn. Composition of
untied cells keeps out-degree at most one; tying is what breaks it. The cell also
fails as a substitute for Willems: its two edges share a target (`cdl_has_cofork`).
-/

open CategoryTheory

/-- The three positions of a parametric map `(P, f : P × A → B)`. -/
inductive CDLPosition
  | parameter
  | input
  | output
  deriving DecidableEq, Inhabited

/-- The generating arrows of the parametric-map quiver, in the functional
direction: `f` reads the parameter and the input and produces the output. -/
inductive CDLArrow : CDLPosition → CDLPosition → Type
  | apply_parameter : CDLArrow .parameter .output
  | apply_input : CDLArrow .input .output

instance : Quiver CDLPosition where
  Hom := CDLArrow

/-- The shape category of a single parametric map. -/
abbrev CDLShape := Paths CDLPosition

/-- Embedding `I_Klir` into `I_CDL`: relation ↦ parameter, things ↦ output. The
weights are the relation, as in the Myers row where the state is. -/
def klirToCDLPre : Prefunctor KlirPosition (Paths CDLPosition) where
  obj | .things => .output | .relation => .parameter
  map | .relation_on_things => Quiver.Hom.toPath CDLArrow.apply_parameter

def klirToCDL : Paths KlirPosition ⥤ Paths CDLPosition :=
  Paths.lift klirToCDLPre

theorem klirToCDL_obj_injective : Function.Injective klirToCDLPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [klirToCDLPre]

theorem klirToCDL_faithful : klirToCDL.Faithful := faithful_of_subsingleton_hom _

namespace SharedPrimitive

/-- The Klir arrow embeds at the quiver level: edge to edge, injective on vertices. -/
def klirToCDLQuiver : QuiverEmbedding KlirPosition CDLPosition where
  toPre :=
    { obj := fun | .things => .output | .relation => .parameter
      map := fun | .relation_on_things => CDLArrow.apply_parameter }
  obj_inj := by intro a b h; cases a <;> cases b <;> simp_all
  map_inj := by
    intro x y e f _
    cases e; cases f; rfl

/-- Every vertex of the parametric-map quiver has out-degree at most one. -/
theorem cdl_out_degree_le_one {a b c : CDLPosition} (e : a ⟶ b) (f : a ⟶ c) :
    b = c := by
  cases e <;> cases f <;> rfl

/-- The parametric-map quiver has a cofork: two distinct sources, one target. It
therefore cannot replace Willems. -/
theorem cdl_has_cofork :
    ∃ (x y z : CDLPosition) (_ : x ⟶ z) (_ : y ⟶ z), x ≠ y :=
  ⟨.parameter, .input, .output, CDLArrow.apply_parameter, CDLArrow.apply_input,
    by decide⟩

variable {V : Type*} [Quiver V]

/-- No fork, from the parametric-map shape alone. -/
theorem no_fork_cdl (eC : QuiverEmbedding V CDLPosition) {x y z : V}
    (e : x ⟶ y) (f : x ⟶ z) : y = z :=
  eC.obj_inj (cdl_out_degree_le_one (eC.toPre.map e) (eC.toPre.map f))

/-- `zigzag_confined` with the parametric-map shape in place of Joslyn. -/
theorem zigzag_confined_cdl (eC : QuiverEmbedding V CDLPosition)
    (eW : QuiverEmbedding V WillemsPosition) {x y : V} (e : x ⟶ y) :
    ∀ {w : V}, Zigzag x w → w = x ∨ w = y := by
  intro w hw
  induction hw with
  | refl => exact Or.inl rfl
  | fwd _ g ih =>
      rcases ih with rfl | rfl
      · exact Or.inr (no_fork_cdl eC e g).symm
      · exact (no_two_chain eW e g).elim
  | bwd _ g ih =>
      rcases ih with rfl | rfl
      · exact (no_two_chain eW g e).elim
      · exact Or.inl (no_cofork eW e g).symm

/-- **A parametric map can stand in for Joslyn.** A connected quiver embedding into
the parametric-map and Willems shapes, with at least one edge, has exactly two
vertices and exactly one edge. -/
theorem connected_is_single_arrow_cdl
    (eC : QuiverEmbedding V CDLPosition) (eW : QuiverEmbedding V WillemsPosition)
    (conn : ∀ a b : V, Zigzag a b) {x y : V} (e : x ⟶ y) :
    x ≠ y ∧ (∀ w : V, w = x ∨ w = y) ∧ ∀ (u v : V) (_ : u ⟶ v), u = x ∧ v = y := by
  refine ⟨?_, fun w => zigzag_confined_cdl eC eW e (conn x w), ?_⟩
  · rintro rfl; exact no_loop eW e
  · intro u v f
    rcases zigzag_confined_cdl eC eW e (conn x u) with rfl | rfl
    · exact ⟨rfl, (no_fork_cdl eC e f).symm⟩
    · exact (no_two_chain eW e f).elim

/-! ## Separating instance: weight tying -/

/-- Two cells sharing one parameter, the shape of a tied weight. -/
inductive TiedPosition
  | parameter
  | input₁
  | output₁
  | input₂
  | output₂
  deriving DecidableEq

inductive TiedArrow : TiedPosition → TiedPosition → Type
  | apply_parameter₁ : TiedArrow .parameter .output₁
  | apply_input₁ : TiedArrow .input₁ .output₁
  | apply_parameter₂ : TiedArrow .parameter .output₂
  | apply_input₂ : TiedArrow .input₂ .output₂

instance : Quiver TiedPosition where
  Hom := TiedArrow

/-- Weight tying is a fork: one parameter vertex, two distinct outputs. -/
theorem tied_has_fork :
    ∃ (x y z : TiedPosition) (_ : x ⟶ y) (_ : x ⟶ z), y ≠ z :=
  ⟨.parameter, .output₁, .output₂, TiedArrow.apply_parameter₁,
    TiedArrow.apply_parameter₂, by decide⟩

/-- The tied shape does not embed into the untied cell, so the forcing property
of `connected_is_single_arrow_cdl` is a property of untied cells only. -/
theorem tied_no_embedding_into_cdl : ¬ Nonempty (QuiverEmbedding TiedPosition CDLPosition) := by
  rintro ⟨eC⟩
  have := no_fork_cdl eC TiedArrow.apply_parameter₁ TiedArrow.apply_parameter₂
  exact absurd this (by decide)

end SharedPrimitive
