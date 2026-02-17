/-
  Systems/Core/Thing.lean
  Things, parthood, and composition

  Formalizes Bunge, Treatise on Basic Philosophy Vol. 4, §1.1-1.2:
  - Parthood as a preorder on things (reflexive, transitive)
  - Composition C(x) = {y | y ⊑ x}
  - A-composition C_A(x) = C(x) ∩ A

  DESIGN: Things are parametrized as an opaque type α with a Preorder
  instance representing the parthood relation ⊑. This allows any concrete
  domain (molecules, organisms, social units) to instantiate the framework.
-/

import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Set.Basic

namespace Systems

/-! ## Parthood and Composition -/

/-- The composition of a thing x is the set of all its parts.
    Bunge §1.2: C(x) = {y ∈ Θ | y ⊑ x} where ⊑ is parthood.
    Here, parthood is the ≤ relation of the Preorder on α. -/
def Composition {α : Type*} [Preorder α] (x : α) : Set α :=
  {y | y ≤ x}

/-- The A-composition of a thing x is the set of its parts that belong to A.
    Bunge §1.2: C_A(x) = C(x) ∩ A = {y ∈ A | y ⊑ x}. -/
def AComposition {α : Type*} [Preorder α] (A : Set α) (x : α) : Set α :=
  {y ∈ A | y ≤ x}

/-- A-composition equals the intersection of Composition with A.
    Bunge §1.2: C_A(x) = C(x) ∩ A. -/
theorem aComposition_eq_inter {α : Type*} [Preorder α] (A : Set α) (x : α) :
    AComposition A x = Composition x ∩ A := by
  ext y
  simp [AComposition, Composition, Set.mem_inter_iff]
  exact ⟨fun ⟨ha, hle⟩ => ⟨hle, ha⟩, fun ⟨hle, ha⟩ => ⟨ha, hle⟩⟩

/-- Every thing is part of itself (reflexivity of parthood).
    Immediate from Preorder. -/
theorem self_mem_composition {α : Type*} [Preorder α] (x : α) :
    x ∈ Composition x :=
  le_refl x

/-- If y is part of x and z is part of y, then z is part of x (transitivity).
    Immediate from Preorder. -/
theorem composition_trans {α : Type*} [Preorder α] {x y z : α}
    (hzy : z ∈ Composition y) (hyx : y ∈ Composition x) :
    z ∈ Composition x :=
  le_trans hzy hyx

end Systems
