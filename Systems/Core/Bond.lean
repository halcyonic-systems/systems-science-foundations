/-
  Systems/Core/Bond.lean
  Action, bonding, and bondage

  Formalizes Bunge, Treatise on Basic Philosophy Vol. 4, §1.2 and §2.2:
  - ActsOn a b: thing a modifies the trajectory of thing b
  - Bonded a b: at least one acts on the other
  - Bondage of a set: the set of all bonded pairs

  Bunge §2.2 item (x): A(x,y) = h(y|x) ∩ h̄(y) — action is the difference
  between the forced and free trajectory of the patient.

  DESIGN: ActsOn is a Prop-valued relation parametrized by a state space type.
  This is abstract enough for the general ontology, but concrete enough
  that BRA can provide computational evidence (State.apply changes trajectory).
-/

import Systems.Core.Thing

namespace Systems

/-! ## State Space -/

/-- A type α has an associated state space S.
    This provides the substrate for defining "modifies trajectory". -/
class HasStateSpace (α : Type*) (S : outParam (Type*))

/-! ## Action -/

/-- Thing a acts on thing b: a modifies b's behavior/trajectory/history.
    Bunge §1.2: a ▷ b symbolizes the acting of thing a on thing b.
    Bunge §2.2 item (x): A(x,y) = h(y|x) ∩ h̄(y), the difference
    between forced and free trajectory.

    This is abstract (Prop-valued) — concrete instances provide evidence. -/
class ActsOn (α : Type*) where
  actsOn : α → α → Prop

export ActsOn (actsOn)

/-- Notation: a ▷ b for "a acts on b" (Bunge's symbol). -/
scoped infixl:50 " ▷ " => actsOn

/-! ## Bond -/

/-- Two things are bonded if at least one acts on the other.
    Bunge §1.2: "two things are connected if at least one of them
    acts on the other."
    Note: bonding is symmetric but ActsOn is not — the asymmetry
    (agent vs. patient) is important. -/
def Bonded {α : Type*} [ActsOn α] (a b : α) : Prop :=
  a ▷ b ∨ b ▷ a

/-- Bonded is symmetric by definition. -/
theorem bonded_comm {α : Type*} [ActsOn α] (a b : α) :
    Bonded a b ↔ Bonded b a := by
  simp [Bonded, or_comm]

/-! ## Bondage -/

/-- The bondage of a set X is the set of all bonded pairs within X.
    Bunge §1.2: B_A is the set of bonds among the things in A. -/
def Bondage {α : Type*} [ActsOn α] (X : Set α) : Set (α × α) :=
  {p | p.1 ∈ X ∧ p.2 ∈ X ∧ Bonded p.1 p.2}

/-- The set of non-bonding relations: complement of Bondage in the
    total relation set on X.
    Bunge §1.2: B̄_A, the nonbonding relations. -/
def NonBondingRelations {α : Type*} [ActsOn α] (X : Set α)
    (R : Set (α × α)) : Set (α × α) :=
  {p ∈ R | p.1 ∈ X ∧ p.2 ∈ X ∧ ¬Bonded p.1 p.2}

/-- If a acts on b and both are in X, then (a,b) is in the bondage of X. -/
theorem actsOn_mem_bondage {α : Type*} [ActsOn α] {X : Set α} {a b : α}
    (ha : a ∈ X) (hb : b ∈ X) (hab : a ▷ b) :
    (a, b) ∈ Bondage X :=
  ⟨ha, hb, Or.inl hab⟩

end Systems
