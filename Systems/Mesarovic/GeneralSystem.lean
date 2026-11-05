/-
  Systems/Mesarovic/GeneralSystem.lean
  Mesarović & Takahara 1975, Definition 1.1: the general system as a relation

  Source: Mesarović & Takahara, General Systems Theory: Mathematical
  Foundations (Academic Press, 1975), Ch. II §1(a), Definition 1.1, book
  p. 11, eqs. (2.1)–(2.2); atlas entry mesarovic-takahara-1975-general-system.

  "Definition 1.1. A (general) system is a relation on nonempty (abstract)
  sets S ⊂ ×{Vᵢ : i ∈ I} (2.1), where × denotes Cartesian product and I
  is the index set. A component set Vᵢ is referred to as a system object."

  The shape file (Systems/Category/ShapeMesarovic.lean) encodes Def 1.2
  (the I/O partition) and Def 1.4 (the global state), not Def 1.1: a
  relation on a product has no dependency between its coordinates to draw
  as an arrow, so Def 1.1 lives here at the data level, as Rosen's pair
  does in ViewGeneration.lean.

  Joslyn's Def 5 (Systems/Joslyn/JoslynSystem.lean) adopts this definition
  from "the Mesarovic school" and adds S ≠ ∅; `JoslynSystem.toMesarovic`
  is the forgetful map from the species to the genus.
-/

import Mathlib.Data.Set.Basic
import Systems.Joslyn.JoslynSystem
import Systems.Tools.Atlas

namespace Systems

/-- Mesarović & Takahara's general system (1975, Def 1.1): a relation on a
    family of nonempty abstract sets, `S ⊂ ×{Vᵢ : i ∈ I}`. `ι` is the index
    set I; `V i` the system object Vᵢ.

    What is committed to: the component sets are nonempty (`nonempty`, the
    definition's "nonempty (abstract) sets"). What is not: the relation
    itself may be empty, which the definition does not forbid; Joslyn's
    Def 5 adds exactly that clause (`JoslynSystem.nonempty`). The page
    prints ⊂; `Set` reads it as a subset, proper or not, as every other
    file here reads Mesarović's inclusion. -/
@[atlas "mesarovic-takahara-1975-general-system"]
structure MesarovicSystem (ι : Type*) (V : ι → Type*) where
  /-- S: the relation on the product of the system objects. -/
  relation : Set (∀ i, V i)
  /-- "nonempty (abstract) sets": each system object Vᵢ is inhabited. -/
  nonempty : ∀ i, Nonempty (V i)

/-- A witness state of a Joslyn system inhabits every coordinate: each
    dimensional distinction is nonempty once one admitted state exists. -/
theorem JoslynSystem.nonempty_coord {ι : Type*} {X : ι → Type*}
    (J : JoslynSystem ι X) (i : ι) : Nonempty (X i) :=
  let ⟨s, _⟩ := J.nonempty
  ⟨s i⟩

/-- The forgetful map from Joslyn's Def 5 to Mesarović's Def 1.1: keep the
    relation, forget that it is nonempty. The coordinate nonemptiness
    Mesarović asks for is supplied by Joslyn's witness state
    (`nonempty_coord`), so nothing is assumed beyond Def 5. -/
def JoslynSystem.toMesarovic {ι : Type*} {X : ι → Type*}
    (J : JoslynSystem ι X) : MesarovicSystem ι X where
  relation := J.states
  nonempty := J.nonempty_coord

/-- The forgetful map keeps the relation exactly. -/
theorem JoslynSystem.toMesarovic_relation {ι : Type*} {X : ι → Type*}
    (J : JoslynSystem ι X) : J.toMesarovic.relation = J.states :=
  rfl

end Systems
