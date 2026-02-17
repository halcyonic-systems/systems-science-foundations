/-
  Systems/Core/Assembly.lean
  Assembly, emergence, and self-organization

  Formalizes Bunge, Treatise on Basic Philosophy Vol. 4, §3.2:
  - Assembly: bondage goes from ∅ to nonempty (Def 1.12)
  - Self-assembly and self-organization (Def 1.12(ii),(iii))
  - Qualitative novelty: symmetric difference of property sets (Def 1.13(i))
  - Emergent properties: set difference on property sets (Def 1.13(ii))
  - Absolutely emergent properties (Def 1.14)
  - Postulate 1.5: every assembly gains and loses properties

  SHOWCASE THEOREM #4: Emergence is precisely characterized by set operations.
-/

import Systems.Core.System

namespace Systems

/-! ## Assembly (Bunge Def 1.12) -/

/-- An assembly event: a thing x with initially no bonds assembles into a
    system y with the same composition but nonempty bondage.
    Bunge Def 1.12(i): x assembles into y at t' > t iff
    C(y,t') = C(x,t) ∧ B(y,t') ≠ ∅ (while B(x,t) = ∅). -/
structure Assembly (α : Type*) [ActsOn α] where
  /-- The initial thing (aggregate, no bonds) -/
  precursor : ConcreteSystem α
  /-- The resulting system (with bonds) -/
  result : ConcreteSystem α
  /-- Composition is preserved -/
  composition_preserved : result.composition = precursor.composition
  /-- The precursor had empty internal structure (no bonds) -/
  precursor_unbonded : precursor.internalStructure = ∅
  /-- The result has nonempty bondage (is a genuine system) -/
  result_bonded : result.internalStructure ≠ ∅

/-- Self-assembly: the assembly occurs naturally (without external guidance).
    Bunge Def 1.12(ii): the aggregate turns "by itself" into the system.

    DESIGN: We represent "natural" as an opaque predicate since Bunge
    doesn't formalize "by itself" further. -/
structure SelfAssembly (α : Type*) [ActsOn α] extends Assembly α where
  /-- The process is spontaneous (natural, not artificial) -/
  spontaneous : Prop

/-- Self-organization: self-assembly where the result contains subsystems
    that did not exist before.
    Bunge Def 1.12(iii): new subsystems come into being. -/
structure SelfOrganization (α : Type*) [ActsOn α] extends SelfAssembly α where
  /-- New subsystems that arise (not present in precursor) -/
  newSubsystems : Set (ConcreteSystem α)
  /-- The new subsystems are nonempty -/
  new_nonempty : newSubsystems.Nonempty

/-! ## Properties and Emergence (Bunge Def 1.13) -/

/-- Properties of a thing at a given time.
    Bunge: p_x(t) is the collection of properties of thing x at time t.
    We represent properties as a Set over an abstract property type. -/
structure PropertySnapshot (P : Type*) where
  /-- The set of properties at this time -/
  properties : Set P

/-- Qualitative novelty: the symmetric difference of property sets.
    Bunge Def 1.13(i): n_x(t,t') = p_x(t) △ ∪_{t<τ≤t'} p_x(τ)

    We simplify to comparing two snapshots (before and after). -/
def qualitativeNovelty {P : Type*}
    (before after : PropertySnapshot P) : Set P :=
  (before.properties \ after.properties) ∪ (after.properties \ before.properties)

/-- Emergent properties: new properties that appear.
    Bunge Def 1.13(ii): e_x(t,t') = ∪_{t<τ≤t'} p_x(τ) - p_x(t)

    Properties in the later state that were not in the earlier state. -/
def emergentProperties {P : Type*}
    (before after : PropertySnapshot P) : Set P :=
  after.properties \ before.properties

/-- Lost properties: properties that disappear.
    Complement of emergence within qualitative novelty. -/
def lostProperties {P : Type*}
    (before after : PropertySnapshot P) : Set P :=
  before.properties \ after.properties

/-- Qualitative novelty is the union of emergent and lost properties.
    This is the showcase: emergence is precisely set operations, not mystical. -/
theorem novelty_eq_emergent_union_lost {P : Type*}
    (before after : PropertySnapshot P) :
    qualitativeNovelty before after =
      lostProperties before after ∪ emergentProperties before after := by
  simp [qualitativeNovelty, emergentProperties, lostProperties]

/-- Emergence implies qualitative novelty (if anything emerged, there is novelty). -/
theorem emergent_sub_novelty {P : Type*}
    (before after : PropertySnapshot P) :
    emergentProperties before after ⊆ qualitativeNovelty before after := by
  intro x hx
  simp [qualitativeNovelty, emergentProperties] at *
  exact Or.inr hx

/-! ## Absolutely Emergent Properties (Bunge Def 1.14) -/

/-- Absolutely emergent properties: properties that have never appeared
    in any thing before.
    Bunge Def 1.14: e^a_x(t,t') = e_x(t,t') - ∪_{y∈Θ, τ≤t'} p_y(τ)
    with y ≠ x.

    Parametrized over a "prior properties" set representing all properties
    ever observed in any other thing. -/
def absolutelyEmergent {P : Type*}
    (before after : PropertySnapshot P) (priorInUniverse : Set P) : Set P :=
  emergentProperties before after \ priorInUniverse

/-- Absolutely emergent properties are a subset of emergent properties. -/
theorem absolutely_emergent_sub {P : Type*}
    (before after : PropertySnapshot P) (prior : Set P) :
    absolutelyEmergent before after prior ⊆ emergentProperties before after :=
  fun _ hx => hx.1

/-! ## Postulate 1.5: Assembly implies Emergence -/

/-- Bunge Postulate 1.5: Every assembly process is accompanied by the
    emergence of some properties and the loss of others.
    p_x(t) - p_x(t') ≠ ∅ and p_x(t') - p_x(t) ≠ ∅. -/
structure PostulateAssemblyEmergence {P : Type*}
    (before after : PropertySnapshot P) where
  /-- Some properties are gained -/
  gains : (emergentProperties before after).Nonempty
  /-- Some properties are lost -/
  losses : (lostProperties before after).Nonempty

end Systems
