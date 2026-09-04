/-
  Systems/Bunge/AggregateBridge.lean
  SSF #48 target 1 — the two aggregate criteria: bridge or separating instance.

  STATUS: ADOPTED on the product reading (2026-09-04). Build with:
    lake build Systems.Bunge.AggregateBridge

  Bunge gives two criteria for the aggregate/system distinction:

    (1) BOND criterion (Ont. II Def 1.1 / Ont. I Cor 5.14):
        a collection is an aggregate iff it has no internal bonds.
        Encoded: Systems/Core/Systemness.lean `IsAggregate : Set α → Prop`.

    (2) STATE-SPACE criterion (Ont. II §2.2, "p. 640"; Ont. I Def 5.35):
        a thing is an aggregate iff the state of no component is determined
        by the states of the others. Encoded, since 2026-09-04, on the
        PRODUCT of the component state spaces: the one-tick law factors
        coordinate-wise and no joint state is excluded
        (Systems/Core/JointState.lean `IsProductAggregate`).

  Bunge asserts the criteria coextensive (Ont. I claims the derivation at
  Cor 5.14). This file puts both criteria on one object and settles the
  relationship: they are logically INDEPENDENT as formalized, in both
  directions, so Cor 5.14's content is a pair of coupling postulates,
  named at the end as hypotheses and asserted nowhere.

  TWO CARRIERS, AND WHY. `StateCarrier` (JointState.lean) sits on
  `ConcreteSystem`, whose `bondage_nonempty` field (Ont. II Def 1.1) bakes a
  bond into every carrier. So on `StateCarrier` only ONE direction of the
  disagreement can occur: bonded yet product-aggregate (`stateCarrier_organized`
  proves every carrier is organized). The other direction, bond-free yet not
  product-aggregate, needs a carrier that carries the CES data WITHOUT
  Def 1.1: `ProductComposite` below (things + edges + per-thing `Q` + per-edge
  `K`). Every `StateCarrier` is a `ProductComposite` (`StateCarrier.toComposite`),
  and `Factors` transfers definitionally (`factors_toComposite`), so the
  bonded-side witness is exactly `JointState.Neurons.aggregate` viewed on
  the composite. The independence verdict is stated over `ProductComposite`.

  HISTORY. Until 2026-09-04 criterion (2) was encoded as a UNION over one
  shared carrier (`State.isAggregateUnion`, `StatefulComposite.stateAggregateUnion`
  below, both retired, both kept). `JointState.union_misses_neuron_aggregate`
  refutes that reading on Bunge's own three-neuron aggregate. The union
  section at the end of this file is preserved so that the retired theorems
  still compile and can be cited AS theorems about the retired reading.

  Axiom profiles (`#print axioms`, recorded 2026-09-04, Lean v4.28.0):
    stateCarrier_organized                   : (none)
    bonded_yet_productAggregate              : propext, Quot.sound
    bondFree_yet_productSystem               : propext, Quot.sound
    productAggregate_criteria_independent    : propext, Quot.sound
    bondAggregate_iff_productAggregate_of_coupling : propext, Classical.choice, Quot.sound
      (double negation: `bondAggregate` is `¬ IsOrganized`)
    bonded_yet_stateAggregateUnion (retired) : propext, Classical.choice, Quot.sound
    bondFree_yet_stateSystemUnion (retired)  : propext, Classical.choice, Quot.sound
  No sorryAx anywhere. See the `#print axioms` lines at the end of the file.
-/

import Systems.Core.Bond
import Systems.Core.State
import Systems.Core.Systemness
import Systems.Core.JointState
import Mathlib.Data.Set.Lattice

namespace Systems

universe u v w

/- PROOF TARGET: the bond criterion and the product state-space criterion
   for "aggregate" are logically independent over composites carrying both
   a bond relation and a per-component state assignment with a law.

   MATHEMATICAL INTENT:
   Bunge's two systemhood criteria are asserted equivalent (Ont. I Cor 5.14).
   If they are independent as encoded, the equivalence is not ontology but a
   substantive physical postulate (bonding restricts joint dynamics), which
   must enter as a named hypothesis, not a silent assumption.

   AVAILABLE TOOLS:
   `ActsOn`, `Bonded` (Systems/Core/Bond.lean), `IsOrganized`, `IsAggregate`
   (Systems/Core/Systemness.lean), `StateCarrier`, `JointState`,
   `LawfulDynamics`, `Factors`, `IsProductAggregate`, `JointState.Neurons.*`
   (Systems/Core/JointState.lean).

   DOES NOT COUNT:
   - witnesses on an empty or one-point carrier (the criteria must disagree
     on a composite with at least two distinct things; on one component
     every law factors);
   - an `ActsOn` instance whose action relation is `fun _ _ => False` for the
     bonded-side witness (the bond must actually hold);
   - a law that factors trivially because `Q` is a one-point type;
   - defining the coupling postulates and then "proving" equivalence from
     them and calling that a bridge (the equivalence-under-coupling theorem
     at the end is the REPAIRED FORM of Cor 5.14, labelled as such, not a
     bridge);
   - `decide`/`native_decide` for the universal (independence) claims —
     concrete computation is fine for the ∃ witnesses only.
-/

/-! ## The product-side composite: CES data without Def 1.1 -/

/-- A composite carrying BOTH criteria's data on the product reading: a set
    of things with a bond relation (via `ActsOn α`), a set of edges, a state
    type for each thing and a reading type for each edge. This is a
    `StateCarrier` minus `ConcreteSystem.bondage_nonempty` (and minus the
    environment, which neither criterion consults), so that bond-FREE
    composites are expressible at all. -/
structure ProductComposite (α : Type u) [ActsOn α] where
  /-- The things whose bonds criterion (1) inspects and whose states criterion (2) reads. -/
  things : Set α
  /-- Internal links carrying flow readings (Mobus flows; may be empty). -/
  edges : Set (α × α)
  /-- Per-thing state type (Bunge F_i range; Mobus reservoir coordinate). -/
  Q : α → Type v
  /-- Per-edge reading type (`Unit` when unmodeled). -/
  K : α × α → Type w

variable {α : Type u} [ActsOn α]

namespace ProductComposite

/-- The joint state of a composite: one reading per thing and one per edge.
    Same shape as `JointState`; definitionally equal to it on
    `StateCarrier.toComposite`. -/
def State (c : ProductComposite.{u, v, w} α) : Type (max u v w) :=
  ((a : {a // a ∈ c.things}) → c.Q a.1) × ((e : {e // e ∈ c.edges}) → c.K e.1)

/-- Lawful dynamics on a composite (same fields as `LawfulDynamics`). -/
structure Dynamics (c : ProductComposite.{u, v, w} α) where
  /-- Bunge S_L ⊆ product (1979:649). -/
  lawful : Set c.State
  /-- One tick of state change. -/
  law : c.State → c.State
  /-- The law never leaves the lawful subset. -/
  closed : ∀ s ∈ lawful, law s ∈ lawful

/-- The law factors iff each thing's successor depends only on that thing's
    own state (mirror of `JointState.Factors`). -/
def factors (c : ProductComposite.{u, v, w} α) (law : c.State → c.State) : Prop :=
  ∀ a : {a // a ∈ c.things}, ∃ f : c.Q a.1 → c.Q a.1, ∀ s : c.State, (law s).1 a = f (s.1 a)

/-- Criterion (1), bond form, imported from Systemness.lean. -/
def bondAggregate (c : ProductComposite.{u, v, w} α) : Prop :=
  IsAggregate c.things

/-- Criterion (2), product form (mirror of `IsProductAggregate`): the law
    factors and no joint state is excluded. -/
def Dynamics.productAggregate {c : ProductComposite.{u, v, w} α} (d : c.Dynamics) : Prop :=
  c.factors d.law ∧ d.lawful = Set.univ

end ProductComposite

/-! ## Every `StateCarrier` is a composite, and a bonded one -/

/-- Forget Def 1.1 and the environment: a state carrier as a product composite. -/
def StateCarrier.toComposite (c : StateCarrier.{u, v, w} α) : ProductComposite.{u, v, w} α :=
  ⟨c.system.composition, c.system.structure', c.Q, c.K⟩

/-- Lawful dynamics transfer along `toComposite` (the state types coincide
    definitionally). -/
def LawfulDynamics.toComposite {c : StateCarrier.{u, v, w} α} (d : LawfulDynamics c) :
    c.toComposite.Dynamics :=
  ⟨d.lawful, d.law, d.closed⟩

/-- `Factors` on a carrier is `factors` on its composite, definitionally. -/
theorem factors_toComposite (c : StateCarrier.{u, v, w} α) (law : JointState c → JointState c) :
    Factors c law ↔ c.toComposite.factors law :=
  Iff.rfl

/-- `IsProductAggregate` on a carrier is `productAggregate` on its composite. -/
theorem isProductAggregate_toComposite {c : StateCarrier.{u, v, w} α} (d : LawfulDynamics c) :
    IsProductAggregate d ↔ d.toComposite.productAggregate :=
  Iff.rfl

/-- Every state carrier is organized by the bond criterion: `ConcreteSystem`
    carries Def 1.1 as the field `bondage_nonempty`. Consequence: on
    `StateCarrier` the two criteria can disagree only in the direction
    "bonded yet product-aggregate"; the other direction needs
    `ProductComposite`. `#print axioms`: none. -/
theorem stateCarrier_organized (c : StateCarrier.{u, v, w} α) :
    IsOrganized c.toComposite.things :=
  c.system.composition_organized

/-! ## Separating instances on the product -/

open ProductComposite in
/-- Separating instance, direction one: a composite whose things are bonded
    (organized — criterion 1 says SYSTEM) while its law factors on the full
    product (criterion 2 says AGGREGATE). A bond with no dynamical
    consequence: nothing in the encoded ontology forbids it.
    Witness: Bunge's three neurons on the ring wiring `a ▷ a + 1`
    (`JointState.Neurons.threeNeurons`) under the identity law
    (`JointState.Neurons.aggregate`). `#print axioms`: propext, Quot.sound. -/
theorem bonded_yet_productAggregate :
    ∃ (α : Type) (inst : ActsOn α) (c : @ProductComposite.{0, 0, 0} α inst)
      (d : c.Dynamics), IsOrganized c.things ∧ d.productAggregate := by
  open JointState.Neurons in
  exact ⟨Fin 3, inferInstance, carrier.toComposite, aggregate.toComposite,
    stateCarrier_organized carrier,
    (isProductAggregate_toComposite aggregate).mp identity_isProductAggregate⟩

namespace ProductComposite.Swap

/-- No thing acts on any other: the bond-free wiring. Scoped to the witness. -/
scoped instance : ActsOn Bool := ⟨fun _ _ => False⟩

/-- Two things, each carrying a `Bool`, no edges, no bonds. -/
def composite : ProductComposite.{0, 0, 0} Bool where
  things := Set.univ
  edges := ∅
  Q := fun _ => Bool
  K := fun _ => Unit

/-- The swap law: each thing takes the OTHER thing's state. Flows untouched. -/
def swapLaw : composite.State → composite.State :=
  fun s => (fun a => s.1 ⟨!a.1, Set.mem_univ _⟩, s.2)

/-- Every joint state lawful, swap law. -/
def dynamics : composite.Dynamics where
  lawful := Set.univ
  law := swapLaw
  closed := fun _ _ => Set.mem_univ _

/-- A joint state with the given readings and trivial flow readings. -/
private def mk (f : Bool → Bool) : composite.State :=
  (fun a => f a.1, fun e => e.2.elim)

/-- The composite has no internal bonds. -/
theorem bondFree : composite.bondAggregate := by
  rintro ⟨a, -, b, -, -, hbond⟩
  rcases hbond with h | h <;> exact h

/-- The swap law does not factor: thing `true`'s successor is thing `false`'s
    state (compare `(false, false)` with `(false, true)`). -/
theorem swap_not_factors : ¬ composite.factors swapLaw := by
  intro h
  obtain ⟨f, hf⟩ := h ⟨true, Set.mem_univ _⟩
  have h0 := hf (mk fun _ => false)
  have h1 := hf (mk fun b => !b)
  simp [swapLaw, mk] at h0 h1
  revert h0 h1
  cases f false <;> simp

end ProductComposite.Swap

/-- Separating instance, direction two: a composite with no internal bonds
    (criterion 1 says AGGREGATE) whose law does not factor (criterion 2 says
    SYSTEM). Correlation without connection: the encoded ontology does not
    rule it out either. Witness: two unbonded `Bool` cells under the swap
    law (`ProductComposite.Swap`). Not expressible on `StateCarrier`
    (`stateCarrier_organized`). `#print axioms`: propext, Quot.sound. -/
theorem bondFree_yet_productSystem :
    ∃ (α : Type) (inst : ActsOn α) (c : @ProductComposite.{0, 0, 0} α inst)
      (d : c.Dynamics), c.bondAggregate ∧ ¬ d.productAggregate := by
  open ProductComposite.Swap in
  exact ⟨Bool, inferInstance, composite, dynamics, bondFree,
    fun h => swap_not_factors h.1⟩

/-- The verdict, packaged: neither criterion implies the other over
    `ProductComposite`. Follows from the two witnesses.
    `#print axioms`: propext, Quot.sound. -/
theorem productAggregate_criteria_independent :
    (¬ ∀ (α : Type) (inst : ActsOn α) (c : @ProductComposite.{0, 0, 0} α inst)
        (d : c.Dynamics), d.productAggregate → c.bondAggregate) ∧
    (¬ ∀ (α : Type) (inst : ActsOn α) (c : @ProductComposite.{0, 0, 0} α inst)
        (d : c.Dynamics), c.bondAggregate → d.productAggregate) := by
  constructor
  · intro hall
    obtain ⟨α, inst, c, d, horg, hprod⟩ := bonded_yet_productAggregate
    exact hall α inst c d hprod horg
  · intro hall
    obtain ⟨α, inst, c, d, hbf, hps⟩ := bondFree_yet_productSystem
    exact hps (hall α inst c d hbf)

/-! ## Cor 5.14, repaired: the equivalence IS the postulate pair

The two halves of Ont. I Cor 5.14's claimed equivalence, as explicit
coupling hypotheses over a composite and its dynamics (memo §E.3):

  couplingForward  : IsOrganized c.things → ¬ d.productAggregate
    "a bond shows up in the joint dynamics" — the physically substantive
    half; this is what Bunge's prose actually argues. FALSE in general
    (`bonded_yet_productAggregate`), so it is content, not bookkeeping.

  couplingBackward : ¬ d.productAggregate → IsOrganized c.things
    "dynamical dependence only from bonds" — a locality/no-conspiracy
    postulate Bunge never states. FALSE in general
    (`bondFree_yet_productSystem`).

They stay HYPOTHESES, never axioms (no-silent-axioms rule). The alternative
the memo records, and which is deliberately NOT taken here: redefine
`ActsOn` dynamically, as "b's successor depends on a's coordinate". That
would make `couplingForward` definitional (a bond just IS a non-factoring
dependence) and leave `couplingBackward` as the one no-conspiracy postulate;
it would also unbond the three-neuron ring under the identity law, since a
wire nobody's successor reads is then not a bond. That is a change to
`Bond.lean`'s meaning across the whole tree and is a separate decision. -/

/-- Cor 5.14 in repaired form: under both coupling hypotheses, the bond
    criterion and the product criterion coincide. The immediacy of the
    proof is the point — the equivalence is exactly the postulate pair.
    `#print axioms`: propext, Classical.choice, Quot.sound (the forward
    direction eliminates a double negation). -/
theorem bondAggregate_iff_productAggregate_of_coupling
    {c : ProductComposite.{u, v, w} α} (d : c.Dynamics)
    (couplingForward : IsOrganized c.things → ¬ d.productAggregate)
    (couplingBackward : ¬ d.productAggregate → IsOrganized c.things) :
    c.bondAggregate ↔ d.productAggregate := by
  constructor
  · intro hbf
    by_contra hnp
    exact hbf (couplingBackward hnp)
  · intro hp horg
    exact couplingForward horg hp

/-! ## RETIRED union reading (2026-09-04), kept so its theorems still compile

Everything below is ABOUT THE RETIRED READING of Bunge 1979 p. 640 as a
union over one shared state carrier. `JointState.union_misses_neuron_aggregate`
shows that reading classifies Bunge's own three-neuron aggregate as a
system. The witnesses here are union-specific and do not transfer to the
product; the product-side witnesses above replace them. -/

/-- RETIRED carrier for the union reading: things + per-thing state SETS on
    one shared `S` + a total space on that same `S`. Kept for the retired
    theorems only; the live carrier is `ProductComposite`. -/
structure StatefulComposite (α : Type*) (S : Type*) [ActsOn α] where
  things : Set α
  stateOf : α → Set S
  totalSpace : Set S

namespace StatefulComposite

variable {α S : Type*} [ActsOn α]

/-- Criterion (1), bond form, on the retired carrier. -/
def bondAggregate (c : StatefulComposite α S) : Prop :=
  IsAggregate c.things

/-- RETIRED 2026-09-04: the union reading of Bunge 1979 p.640 misclassifies
    Bunge's own three-neuron aggregate (1977, {0,1}^3); see
    `JointState.union_misses_neuron_aggregate`. Replaced by
    `IsProductAggregate` (and `ProductComposite.productAggregate` here).

    Retired definition: total space = indexed union of the parts' spaces. -/
def stateAggregateUnion (c : StatefulComposite α S) : Prop :=
  c.totalSpace = ⋃ x ∈ c.things, c.stateOf x

/-- RETIRED 2026-09-04: the union reading of Bunge 1979 p.640 misclassifies
    Bunge's own three-neuron aggregate (1977, {0,1}^3); see
    `JointState.union_misses_neuron_aggregate`. Replaced by
    `IsProductAggregate`. Deprecated alias of `stateAggregateUnion`. -/
@[deprecated stateAggregateUnion (since := "2026-09-04")]
alias stateAggregate := stateAggregateUnion

/-- ABOUT THE RETIRED READING. A bonded composite whose joint space is exactly
    the union of its parts'. `#print axioms`: propext, Classical.choice,
    Quot.sound. -/
theorem bonded_yet_stateAggregateUnion :
    ∃ (α S : Type) (inst : ActsOn α) (c : @StatefulComposite α S inst),
      IsOrganized c.things ∧ c.stateAggregateUnion := by
  letI inst : ActsOn Bool := ⟨fun a b => a = true ∧ b = false⟩
  refine ⟨Bool, Unit, inst,
    ⟨Set.univ, fun _ => Set.univ, Set.univ⟩, ?_, ?_⟩
  · exact ⟨true, Set.mem_univ _, false, Set.mem_univ _, by decide,
      Or.inl ⟨rfl, rfl⟩⟩
  · show Set.univ = ⋃ x ∈ (Set.univ : Set Bool), (Set.univ : Set Unit)
    ext u
    simp

/-- ABOUT THE RETIRED READING. An unbonded composite whose joint space
    strictly exceeds the union of its parts'. The witness is union-specific:
    it exhibits a point outside the union, which the product reading never
    asks for. `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem bondFree_yet_stateSystemUnion :
    ∃ (α S : Type) (inst : ActsOn α) (c : @StatefulComposite α S inst),
      c.bondAggregate ∧ ¬c.stateAggregateUnion := by
  letI inst : ActsOn Bool := ⟨fun _ _ => False⟩
  refine ⟨Bool, Bool, inst,
    ⟨Set.univ, fun _ => {false}, Set.univ⟩, ?_, ?_⟩
  · rintro ⟨a, -, b, -, -, hbond⟩
    rcases hbond with h | h <;> exact h
  · intro h
    have : (true : Bool) ∈ ⋃ x ∈ (Set.univ : Set Bool), ({false} : Set Bool) := by
      rw [← h]; exact Set.mem_univ _
    simp at this

/-- Deprecated alias of `bonded_yet_stateAggregateUnion` (retired reading). -/
@[deprecated bonded_yet_stateAggregateUnion (since := "2026-09-04")]
alias bonded_yet_stateAggregate := bonded_yet_stateAggregateUnion

/-- Deprecated alias of `bondFree_yet_stateSystemUnion` (retired reading). -/
@[deprecated bondFree_yet_stateSystemUnion (since := "2026-09-04")]
alias bondFree_yet_stateSystem := bondFree_yet_stateSystemUnion

/-- ABOUT THE RETIRED READING. Independence of the bond criterion and the
    UNION criterion over `StatefulComposite`. Superseded by
    `productAggregate_criteria_independent`. -/
theorem aggregate_criteria_independent :
    (¬ ∀ (α S : Type) (inst : ActsOn α) (c : @StatefulComposite α S inst),
        c.stateAggregateUnion → c.bondAggregate) ∧
    (¬ ∀ (α S : Type) (inst : ActsOn α) (c : @StatefulComposite α S inst),
        c.bondAggregate → c.stateAggregateUnion) := by
  constructor
  · intro hall
    obtain ⟨α, S, inst, c, horg, hstate⟩ := bonded_yet_stateAggregateUnion
    exact hall α S inst c hstate horg
  · intro hall
    obtain ⟨α, S, inst, c, hbf, hss⟩ := bondFree_yet_stateSystemUnion
    exact hss (hall α S inst c hbf)

end StatefulComposite

#print axioms stateCarrier_organized
#print axioms bonded_yet_productAggregate
#print axioms bondFree_yet_productSystem
#print axioms productAggregate_criteria_independent
#print axioms bondAggregate_iff_productAggregate_of_coupling
#print axioms StatefulComposite.bonded_yet_stateAggregateUnion
#print axioms StatefulComposite.bondFree_yet_stateSystemUnion

end Systems
