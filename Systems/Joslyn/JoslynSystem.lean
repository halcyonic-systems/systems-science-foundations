/-
  Systems/Joslyn/JoslynSystem.lean
  Joslyn's System₁ — the fourth vertex, set-theoretic tier
  (categorification roadmap Phase 4.1 + 4.3)

  Joslyn, "Semantic Control Systems" (World Futures 45:87-123, 1995).
  Def 5: a system is a nonempty constrained subset of a product of
  dimensional distinctions, S ⊆ X₁ × ... × Xₙ with S ≠ ∅ — Mesarovic's
  relational system, with the nonemptiness DEFINITIONAL.
  Def 21 (synthetic): "A system is a cardinal distinction on a variety of
  dimensional distinctions" — the system is equivalently given by its
  CONSTRAINT C = X − S, what it excludes.

  The Joslyn→Klir projection (§4.3) is clean: flatten the carrier to T,
  the constrained states to R. THE SEAM: Joslyn's Def 5 excludes exactly
  the Klir systems with empty relation or partial thing-set —
  `mem_range_toKlir_iff` is the first machine-checked divergence on the
  Joslyn edge of the ontological diagram.

  The categorical shape (the cyclic feedback quiver) lives separately in
  Systems/Category/ShapeJoslyn.lean; Control₁/Control₂ (Defs 25/28,
  Prop 29) are Phase 4.2, deliberately out of scope here.
-/

import Mathlib.Data.Set.BooleanAlgebra
import Systems.Klir.KlirSystem

namespace Systems

/-! ## Joslyn's System₁ (Def 5) -/

/-- Joslyn's System₁ (1995, Def 5): a nonempty constrained subset of a
    product of dimensional distinctions, `S ⊆ ∏ᵢ Xᵢ`, `S ≠ ∅`.
    Mesarovic's relational system; `ι` indexes the dimensional variety,
    `X i` the distinctions along dimension `i`. Nonemptiness is
    definitional — a system with no admitted states draws no distinction. -/
structure JoslynSystem (ι : Type*) (X : ι → Type*) where
  /-- S: the constrained (admitted) states within the product space. -/
  states : Set (∀ i, X i)
  /-- Def 5's S ≠ ∅ — an empty system draws no cardinal distinction. -/
  nonempty : states.Nonempty

/-- The binary Joslyn system (the paper's worked examples, and the bridge
    to Klir): a nonempty relation on a single carrier. -/
structure JoslynSystem₂ (α : Type*) where
  /-- S: the constrained states, as a binary relation. -/
  states : Set (α × α)
  /-- Def 5's S ≠ ∅. -/
  nonempty : states.Nonempty

/-! ## The constraint (Def 21)

  Joslyn's synthetic definition: a system is a cardinal distinction on a
  variety of dimensional distinctions — equivalently given by what it
  EXCLUDES, the constraint `C = X − S`. -/

/-- The constraint of a Joslyn system: `C = X − S`, everything the system
    excludes (Def 21). The environment is DERIVED from the distinction,
    not primitive — the ontological seam with Bunge's CES triple, where E
    is a given (Phase 4.4, out of scope here). -/
def JoslynSystem.constraint {ι : Type*} {X : ι → Type*}
    (J : JoslynSystem ι X) : Set (∀ i, X i) :=
  J.statesᶜ

/-- Binary version of the Def 21 constraint. -/
def JoslynSystem₂.constraint {α : Type*} (J : JoslynSystem₂ α) : Set (α × α) :=
  J.statesᶜ

/-- The system is recoverable from its constraint: `Cᶜ = S`. Def 21's
    synthetic reading is faithful — specifying what is excluded specifies
    the system.

    FOUNDATIONAL NOTE: this theorem is essentially CLASSICAL
    (`#print axioms` shows `Classical.choice`, via LEM). Double complement
    `Sᶜᶜ = S` is double-negation elimination on membership, unprovable
    constructively — so Joslyn's synthetic definition ("a system IS its
    constraint") is a theorem of classical set theory only. A constructivist
    can pass from system to constraint but not faithfully back. The
    projection theorems below, by contrast, are axiom-free. -/
theorem JoslynSystem.compl_constraint {ι : Type*} {X : ι → Type*}
    (J : JoslynSystem ι X) : J.constraintᶜ = J.states :=
  compl_compl J.states

/-- Binary version: the system is recoverable from its constraint. -/
theorem JoslynSystem₂.compl_constraint {α : Type*} (J : JoslynSystem₂ α) :
    J.constraintᶜ = J.states :=
  compl_compl J.states

/-! ## Projection to Klir (§4.3) — and the seam

  The clean edge of the fourth vertex: flatten the carrier to T, the
  constrained states to R. -/

/-- The Joslyn→Klir projection (roadmap §4.3): the thing-set is the full
    carrier (`⋃ᵢ Xᵢ` read at the binary tier as `univ`), the relation is
    the constrained states. Forgets the constraint's derived-environment
    reading and the nonemptiness — the information loss is characterized
    by `mem_range_toKlir_iff`. -/
def JoslynSystem₂.toKlir {α : Type*} (J : JoslynSystem₂ α) : KlirSystem α where
  things := Set.univ
  relation := J.states

/-- The partial section: a Klir system lifts to Joslyn exactly when its
    relation is nonempty — Def 5 demands a witness Klir does not. -/
def KlirSystem.toJoslyn₂ {α : Type*} (K : KlirSystem α)
    (h : K.relation.Nonempty) : JoslynSystem₂ α where
  states := K.relation
  nonempty := h

/-- The lift is a section on relations: lifting a Klir system to Joslyn
    and projecting back preserves the relation exactly. -/
theorem KlirSystem.toJoslyn₂_toKlir_relation {α : Type*} (K : KlirSystem α)
    (h : K.relation.Nonempty) : ((K.toJoslyn₂ h).toKlir).relation = K.relation :=
  rfl

/- PROOF TARGET: the seam — exactly which Klir systems Joslyn excludes.

   MATHEMATICAL INTENT:
   K is in the image of the Joslyn→Klir projection iff K.relation ≠ ∅ and
   K.things = univ. Joslyn's Def 5 (S ≠ ∅) excludes precisely Klir's
   degenerate systems (empty relation) and partial carriers (things ⊊ univ).
   This is the first machine-checked divergence on the Joslyn edge of the
   ontological diagram: what the fourth vertex refuses to represent.

   AVAILABLE TOOLS:
   - `KlirSystem` is @[ext] (things + relation determine the system)
   - `JoslynSystem₂.toKlir`, `KlirSystem.toJoslyn₂` above

   STRATEGY HINT:
   Forward: destruct the witness, both conjuncts are definitional.
   Backward: lift through toJoslyn₂, close with KlirSystem.ext. -/
theorem KlirSystem.mem_range_toKlir_iff {α : Type*} (K : KlirSystem α) :
    (∃ J : JoslynSystem₂ α, J.toKlir = K) ↔
      K.relation.Nonempty ∧ K.things = Set.univ := by
  constructor
  · rintro ⟨J, rfl⟩
    exact ⟨J.nonempty, rfl⟩
  · rintro ⟨hne, huniv⟩
    refine ⟨K.toJoslyn₂ hne, ?_⟩
    apply KlirSystem.ext
    · exact huniv.symm
    · rfl

end Systems
