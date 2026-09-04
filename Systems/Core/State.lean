/-
  Systems/Core/State.lean
  State functions, lawful state spaces, events, and histories

  Formalizes Bunge, Treatise on Basic Philosophy Vol. 4, §2.2:
  - State function F : A → V₁ × V₂ × ... × Vₙ
  - Conceivable state space S(K): full range of F
  - Lawful state space S_L(K) ⊂ S(K): subset satisfying laws
  - Events as triples ⟨s, s', g⟩
  - Event space E_L(K) ⊆ S_L × S_L
  - History h(x) = {⟨t, F(t)⟩ | t ∈ τ}

  SHOWCASE THEOREM #3: A thing is an aggregate iff its law factors
  component-wise on the full product of its components' state spaces
  (`JointState.Factors` together with `lawful = univ`; see
  `Systems/Core/JointState.lean`, `IsProductAggregate`, and the bridge on it in
  `Systems/Bunge/AggregateBridge.lean`).

  History: until 2026-09-04 this file read Bunge 1979 p. 640 as a UNION of
  component state spaces (`isAggregateUnion` below, retired, kept as a
  deprecated alias `isAggregate`); `JointState.union_misses_neuron_aggregate`
  refutes that reading on Bunge's own three-neuron aggregate.
-/

import Systems.Core.System

namespace Systems

/-! ## State Function (Bunge §2.2) -/

/-- A state function for systems of kind K.
    Bunge §2.2: F = ⟨F₁, F₂, ..., Fₙ⟩ : A → V₁ × V₂ × ... × Vₙ

    We parametrize by:
    - T: the time type
    - S: the state space type (represents the product V₁ × ... × Vₙ)
    - K: the kind of system -/
structure StateFunction (T : Type*) (S : Type*) (K : Type*) where
  /-- The state function maps (system, time) to state -/
  stateAt : K → T → S

/-- The conceivable state space: the full range of the state function.
    Bunge §2.2: S(K) is the range of F.
    All states that any system of kind K could conceivably be in. -/
def conceivableStateSpace {T : Type*} {S : Type*} {K : Type*}
    (F : StateFunction T S K) : Set S :=
  {s | ∃ k t, F.stateAt k t = s}

/-- The lawful state space: a subset of the conceivable space satisfying laws.
    Bunge §2.2: S_L(K) is a proper subset of S(K).
    "Since the components of F are lawfully interrelated, and thus mutually
    restricted, not every n-tuple represents a really possible state."

    Parametrized by a law predicate. -/
def lawfulStateSpace {T : Type*} {S : Type*} {K : Type*}
    (F : StateFunction T S K) (law : S → Prop) : Set S :=
  {s ∈ conceivableStateSpace F | law s}

/-- The lawful state space is a subset of the conceivable one.
    Bunge §2.2: S_L(K) ⊂ S(K). -/
theorem lawful_sub_conceivable {T : Type*} {S : Type*} {K : Type*}
    (F : StateFunction T S K) (law : S → Prop) :
    lawfulStateSpace F law ⊆ conceivableStateSpace F := by
  intro s hs
  exact hs.1

/-! ## Events (Bunge §2.2) -/

/-- An event is a state transition ⟨s, s', g⟩ where g is a lawful map.
    Bunge §2.2(v): every event is representable by ⟨s, s', g⟩ where
    s, s' ∈ S_L(K) and g : S_L(K) → S_L(K) is lawful.

    The path g records how the transition occurs (different paths between
    the same endpoints represent different processes). -/
structure Event (S : Type*) where
  /-- Initial state -/
  initial : S
  /-- Final state -/
  final : S
  /-- The transformation function (path from initial to final) -/
  transition : S → S
  /-- The transition maps initial to final -/
  consistent : transition initial = final

/-- The event space: collection of all lawful events.
    Bunge §2.2(vi): E_L(K) ⊆ S_L(K) × S_L(K).
    "In general the inclusion is proper: not all state transitions are lawful." -/
def eventSpace {S : Type*} (law : S → Prop) (events : Set (Event S)) : Set (S × S) :=
  {p | ∃ e ∈ events, e.initial = p.1 ∧ e.final = p.2 ∧ law p.1 ∧ law p.2}

/-! ## History (Bunge §2.2 item (ix)) -/

/-- The history of a system: the trajectory through state space over time.
    Bunge §2.2(ix): h(x) = {⟨t, F(t)⟩ | t ∈ τ}. -/
def history {T : Type*} {S : Type*} {K : Type*}
    (F : StateFunction T S K) (k : K) (τ : Set T) : Set (T × S) :=
  {p | p.1 ∈ τ ∧ F.stateAt k p.1 = p.2}

/-- Total action of thing x on thing y: the difference between forced and
    free trajectory.
    Bunge 2.2(x): A(x,y) = h(y|x) minus h(y).

    We represent this as the set of time-state pairs where the forced
    and free trajectories differ. -/
def totalAction {T : Type*} {S : Type*}
    (forcedHistory freeHistory : Set (T × S)) : Set (T × S) :=
  {p | p ∈ forcedHistory ∧ p ∉ freeHistory}

/-! ## Aggregate vs System Characterization (Bunge p. 640) — RETIRED union reading

RETIRED 2026-09-04. Bunge p. 640 says an aggregate's state space is "the
union of the partial state spaces". Read literally over one shared carrier,
that union misclassifies Bunge's own three-neuron aggregate (1977, {0,1}^3,
eight points: three embedded two-point spaces cover at most six), see
`JointState.union_misses_neuron_aggregate`. The live criterion is
`JointState.IsProductAggregate` (the law factors component-wise on the full
product); the bridge to the bond criterion is `Systems/Bunge/AggregateBridge.lean`.

The definitions below are kept, renamed `*Union`, so that every theorem
about the retired reading still compiles and can be cited as such. Nothing
here is deleted; the old names survive as deprecated aliases. -/

/-- RETIRED 2026-09-04: the union reading of Bunge 1979 p.640 misclassifies
    Bunge's own three-neuron aggregate (1977, {0,1}^3); see
    `JointState.union_misses_neuron_aggregate`. Replaced by
    `IsProductAggregate`.

    Retired definition: a composite state space is an aggregate iff the total
    state space equals the union of the partial state spaces. -/
def isAggregateUnion {S : Type*}
    (totalSpace : Set S) (componentSpaces : List (Set S)) : Prop :=
  totalSpace = componentSpaces.foldl (· ∪ ·) ∅

/-- RETIRED 2026-09-04: the union reading of Bunge 1979 p.640 misclassifies
    Bunge's own three-neuron aggregate (1977, {0,1}^3); see
    `JointState.union_misses_neuron_aggregate`. Replaced by
    `IsProductAggregate`. Deprecated alias of `isAggregateUnion`. -/
@[deprecated isAggregateUnion (since := "2026-09-04")]
alias isAggregate := isAggregateUnion

/-- ABOUT THE RETIRED READING. A composite is a system (not an aggregate)
    iff the total state space strictly differs from the union of component
    state spaces. "In the case of a system the state of every component is
    determined, at least partly, by the states other system components are
    in." Live form: `¬ IsProductAggregate`. -/
def isSystemByStateSpace {S : Type*}
    (totalSpace : Set S) (componentSpaces : List (Set S)) : Prop :=
  ¬isAggregateUnion totalSpace componentSpaces

/-- ABOUT THE RETIRED READING. If a thing is a union-aggregate, it is not a
    union-system. Bunge p. 640: the two conditions are complementary. This
    relates the criterion only to its own literal negation (SSF #48 vacuity);
    the substantive bridge is `AggregateBridge.lean`. -/
theorem aggregate_not_system {S : Type*}
    (totalSpace : Set S) (componentSpaces : List (Set S))
    (h : isAggregateUnion totalSpace componentSpaces) :
    ¬isSystemByStateSpace totalSpace componentSpaces :=
  fun hn => hn h

/-- ABOUT THE RETIRED READING. If a thing is a union-system, it is not a
    union-aggregate. Same vacuity as `aggregate_not_system`. -/
theorem system_not_aggregate {S : Type*}
    (totalSpace : Set S) (componentSpaces : List (Set S))
    (h : isSystemByStateSpace totalSpace componentSpaces) :
    ¬isAggregateUnion totalSpace componentSpaces :=
  h

end Systems
