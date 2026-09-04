/-
  Systems/Core/JointState.lean
  The component–state bridge: run state as a dependent product indexed by
  the CES triple.

  CANDIDATE, not adopted: existing `State.lean`/`AggregateBridge.lean` untouched.
  Not wired into `Systems.lean`. Build alone with:
    lake build Systems.Core.JointState

  Source: docs/reference/component-state-bridge-memo.md §C (encoding) and
  §D (separating theorem). Every claim below cites that memo's file:line
  form; path prefixes are the memo's (V = the vault's
  operations/systems-science, LC = mobus-lifecycle-paper).

  THREE POSITIONS RECONCILED. They live at two levels: the tuple is not the
  run state, it is the INDEX of the run state.

  (1) Lifecycle tuple = index. The lifecycle paper takes "X = set of ALL
      oct-tuples over chosen carriers = state space. S ∈ X = one oct-tuple =
      one complete description at one moment" (LC/scaffold.md:96-97). Here
      that tuple is `StateCarrier.system` (plus the per-slot carriers `Q`,
      `K`); a lifecycle step re-indexes `JointState`, which is what
      bert-compose does when it clears history on topology change
      (bert-compose/src/circuit.rs:422-424).

  (2) Bunge's lawful subset. The lawful state space "is a subset of the
      cartesian product of the ranges of the components of the state
      function" (V/bunge/Bunge - 1979 - Treatise on Basic Philosophy.md:649,
      Fig. 1.5 caption). That is `LawfulDynamics.lawful ⊆ JointState`.
      Bunge's own aggregate is a product: "for a system composed of 3
      neurons, the state space has 2^3 elements" (V/bunge/Bunge - 1977 -
      Ontology I - The Furniture of the World.md:6794-6796).

  (3) Mobus reservoirs + flows. "Imagine taking a reading on every flow
      (connection) and every reservoir in a system and all of its subsystems
      every Δt instance. The state, σ_i, of the system ..."
      (V/mobus/4-a-model-of-system.md:460). `Q` is the reservoir coordinate
      (one per component), `K` the flow coordinate (one per structure edge;
      `Unit` when unmodeled). "the number of possible states is constrained"
      (:461) is again the `lawful` subset.

  WHAT THE UNION READING GETS WRONG. Bunge 1979:650 says the state space of
  a non-interacting association is "the union of the partial state spaces";
  SSF encodes that at State.lean:114-116 (`isAggregate`, a `List.foldl`
  union) and AggregateBridge.lean:93-94 (`stateAggregate`, an indexed
  union). `union_misses_neuron_aggregate` below shows the union of three
  embedded {0,1}'s has at most 6 points while the three-neuron product has
  8, so the union encoding classifies Bunge's paradigm AGGREGATE as a
  system. The product encoding restates the aggregate criterion as
  `Factors law` (each coordinate's successor depends only on that
  coordinate) together with `lawful = univ`, following the memo's reading
  of Bunge 1979:4488.

  DEVIATIONS FROM THE MEMO'S §C TEXT (all forced by the existing tree):
  - Universe levels are explicit (`Type u`, `Type v`, `Type w`) because
    `Q : α → Type*` inside a structure whose parameter is `Type*` leaves the
    structure's own universe underdetermined; `JointState` lands in
    `Type (max u v w)`.
  - `ConcreteSystem.composition : Set α` and `structure' : Set (α × α)`
    (System.lean:47-53) are `Set`, not `Finset`, so the index types are the
    subtypes `{a // a ∈ composition}` and `{e // e ∈ structure'}` exactly as
    the memo writes them; no Finset conversion was needed.
  - `Factors` quantifies over the subtype index `a : {a // a ∈ composition}`
    and the factor map has type `c.Q a.1 → c.Q a.1`; the memo elides the
    `.1`. Its content is unchanged and it was strong enough for the shift
    counterexample as stated (no strengthening was needed).
  - `IsProductAggregate` (Factors ∧ lawful = univ) is added as the named
    aggregate criterion the memo describes in prose; it is not in the memo's
    code block.
  - A local `ActsOn (Fin 3)` instance (`b = a + 1`, the ring wiring) is
    declared for the witnesses only, scoped to `namespace Systems.JointState.Neurons`.
    No existing `ConcreteSystem (Fin 3)` witness exists in the tree (grep
    2026-09-04), so `threeNeurons` is built here with `environment = ∅`,
    `structure' = {(a, a+1)}`, and the `bondage_nonempty` field satisfied by
    the pair (0, 1).

  Axiom profiles (`#print axioms`, recorded 2026-09-04, Lean v4.28.0):
    union_misses_neuron_aggregate : propext, Classical.choice, Quot.sound
    identity_factors               : propext, Quot.sound
    shift_not_factors              : propext, Quot.sound
    identity_isProductAggregate    : propext, Quot.sound
    shift_not_isProductAggregate   : propext, Quot.sound
  No sorryAx anywhere. The neuron theorems inherit propext/Quot.sound
  through the `Set` membership proofs in `threeNeurons`, not through any
  classical choice. See the `#print axioms` lines at the end of the file.
-/

import Systems.Core.System
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Systems

universe u v w

/-! ## The carrier: a CES triple with per-component and per-flow coordinates -/

/-- A state carrier: a concrete system (the index) with a state set for each
    component and a reading type for each structure edge.
    Memo §C: "Q : α → Type* -- per-component state set (Klir/Bunge/Wymore
    factor); K : α × α → Type* -- per-flow reading (Mobus flows; Unit when
    unmodeled)". Klir: "systems are then conceived as sets of variables
    together with a relation recognized among their state sets"
    (V/klir/klir-facets.md:3533-3534); Wymore's state factor sets
    (V/wymore/wymore-1993-mbse-ch2-systems.md:503-505). -/
structure StateCarrier (α : Type u) [ActsOn α] where
  /-- The CES triple this state is indexed by (lifecycle tuple = index). -/
  system : ConcreteSystem α
  /-- Per-component state set (Mobus reservoir coordinate; Bunge F_i range). -/
  Q : α → Type v
  /-- Per-flow reading type (Mobus flow coordinate; `Unit` when unmodeled). -/
  K : α × α → Type w

variable {α : Type u} [ActsOn α]

/-- The joint (run) state: one reading per component and one per structure
    edge, at fixed structure. Mobus 4-a-model:460 read literally as a
    product over reservoirs and flows. -/
def JointState (c : StateCarrier.{u, v, w} α) : Type (max u v w) :=
  ((a : {a // a ∈ c.system.composition}) → c.Q a.1) ×
  ((e : {e // e ∈ c.system.structure'}) → c.K e.1)

/-- Lawful dynamics on a carrier: Bunge's lawful subset S_L of the product
    (1979:649), and a one-tick law that keeps it (Bunge §2.2(v): g maps
    S_L(K) to S_L(K)). -/
structure LawfulDynamics (c : StateCarrier.{u, v, w} α) where
  /-- Bunge S_L ⊆ product (1979:649). -/
  lawful : Set (JointState c)
  /-- One tick of state change, as in `DynamicSystem.law` (Dynamics.lean:63). -/
  law : JointState c → JointState c
  /-- The law never leaves the lawful subset. -/
  closed : ∀ s ∈ lawful, law s ∈ lawful

/-- A law factors iff each component coordinate's successor depends only on
    that coordinate: the product form of "the state of every component is
    [NOT] determined ... by the states other system components are in"
    (Bunge 1979:650). `DynamicSystem.compose` (Dynamics.lean:91-98) is the
    two-factor instance; `CoupledDynamicSystem.combinedLaw`
    (Dynamics.lean:237-240) in general is not. -/
def Factors (c : StateCarrier.{u, v, w} α) (law : JointState c → JointState c) : Prop :=
  ∀ a : {a // a ∈ c.system.composition},
    ∃ f : c.Q a.1 → c.Q a.1, ∀ s : JointState c, (law s).1 a = f (s.1 a)

/-- The product form of Bunge's aggregate criterion: the law factors and no
    joint state is excluded. Replaces the union test of State.lean:114-116
    (memo §C: "restated as `Factors law` together with `lawful = univ`"). -/
def IsProductAggregate {c : StateCarrier.{u, v, w} α} (d : LawfulDynamics c) : Prop :=
  Factors c d.law ∧ d.lawful = Set.univ

/-! ## Separating theorem (memo §D) -/

/-- Bunge's own three-neuron aggregate (1977:6795-6796) has state space
    {0,1}^3, eight points. Whatever three embeddings of the single-neuron
    space {0,1} one picks, their union has at most six points. So the union
    reading of "aggregate" (State.lean:114-116 `isAggregate`,
    AggregateBridge.lean:93-94 `stateAggregate`) can never equal the
    aggregate's state space, and therefore classifies Bunge's paradigm
    aggregate as a system.

    Proof by cardinality: `Fintype.card (Fin 3 → Bool) = 8`; each range has
    at most 2 elements; three ranges cover at most 3 * 2 = 6
    (`Finset.card_biUnion_le_card_mul`).

    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem union_misses_neuron_aggregate (e : Fin 3 → Bool → (Fin 3 → Bool)) :
    (⋃ i, Set.range (e i)) ≠ Set.univ := by
  intro h
  have hsub : (Finset.univ : Finset (Fin 3 → Bool)) ⊆
      Finset.univ.biUnion (fun i : Fin 3 => Finset.univ.image (e i)) := by
    intro x _
    have hx : x ∈ ⋃ i, Set.range (e i) := h ▸ Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨b, hb⟩ := Set.mem_range.mp hi
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb⟩⟩
  have h1 := Finset.card_le_card hsub
  have h2 : (Finset.univ.biUnion (fun i : Fin 3 => Finset.univ.image (e i))).card ≤
      (Finset.univ : Finset (Fin 3)).card * 2 :=
    Finset.card_biUnion_le_card_mul _ _ 2 (fun i _ =>
      Finset.card_image_le.trans (by simp))
  have h5 : (Finset.univ : Finset (Fin 3 → Bool)).card = 8 := by
    rw [Finset.card_univ, Fintype.card_fun]; rfl
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  omega

/-! ## Companion instances on the three-neuron carrier -/

namespace JointState.Neurons

/-- Ring wiring on three neurons: neuron `a` acts on neuron `a + 1`.
    Scoped to the witnesses; not a global instance. -/
scoped instance : ActsOn (Fin 3) := ⟨fun a b => b = a + 1⟩

/-- The three-neuron system as a CES triple: all three in the composition,
    empty environment, structure = the ring edges (a, a+1). -/
def threeNeurons : ConcreteSystem (Fin 3) where
  composition := Set.univ
  environment := ∅
  structure' := {p | p.2 = p.1 + 1}
  disjoint := Set.inter_empty _
  structure_on := fun _ _ => ⟨Or.inl (Set.mem_univ _), Or.inl (Set.mem_univ _)⟩
  bondage_nonempty := ⟨0, Set.mem_univ _, 1, Set.mem_univ _, by decide, Or.inl rfl⟩

/-- Bunge's three-neuron carrier: each neuron is `Bool` (firing or not),
    flows unmodeled (`Unit`). `JointState` is then (Fin 3 → Bool)-shaped
    on the component side: the eight-point product of 1977:6795-6796. -/
def carrier : StateCarrier.{0, 0, 0} (Fin 3) where
  system := threeNeurons
  Q := fun _ => Bool
  K := fun _ => Unit

/-- The identity law: each neuron keeps its own state. -/
def identityLaw : JointState carrier → JointState carrier := id

/-- Lawful dynamics for the aggregate: every joint state lawful, identity law. -/
def aggregate : LawfulDynamics carrier where
  lawful := Set.univ
  law := identityLaw
  closed := fun _ _ => Set.mem_univ _

/-- The cyclic shift law: neuron `a` takes neuron `a + 1`'s state, flows
    untouched. Memo §D: `law := fun s => (fun a => s.1 (a + 1), s.2)`. -/
def shiftLaw : JointState carrier → JointState carrier :=
  fun s => (fun a => s.1 ⟨a.1 + 1, Set.mem_univ _⟩, s.2)

/-- Lawful dynamics for the system: every joint state lawful, shift law. -/
def system : LawfulDynamics carrier where
  lawful := Set.univ
  law := shiftLaw
  closed := fun _ _ => Set.mem_univ _

/-- The identity law factors: the aggregate. `#print axioms`: propext, Quot.sound. -/
theorem identity_factors : Factors carrier identityLaw :=
  fun _ => ⟨id, fun _ => rfl⟩

/-- Bunge's three-neuron aggregate satisfies the product aggregate
    criterion. `#print axioms`: propext, Quot.sound. -/
theorem identity_isProductAggregate : IsProductAggregate aggregate :=
  ⟨identity_factors, rfl⟩

/-- A joint state with the given component readings and trivial flow readings. -/
private def mk (f : Fin 3 → Bool) : JointState carrier :=
  (fun a => f a.1, fun _ => ())

/-- The shift law does not factor: neuron 0's successor is neuron 1's state,
    so no `f : Bool → Bool` reproduces it (compare the states `(false,false,_)`
    and `(false,true,_)`). The system. `#print axioms`: propext, Quot.sound. -/
theorem shift_not_factors : ¬ Factors carrier shiftLaw := by
  intro h
  obtain ⟨f, hf⟩ := h ⟨0, Set.mem_univ _⟩
  have h0 := hf (mk fun _ => false)
  have h1 := hf (mk fun i => decide (i = 1))
  simp [shiftLaw, mk] at h0 h1
  revert h0 h1
  cases f false <;> simp

/-- The shift system is not a product aggregate. `#print axioms`: propext,
    Quot.sound. -/
theorem shift_not_isProductAggregate : ¬ IsProductAggregate system :=
  fun h => shift_not_factors h.1

end JointState.Neurons

#print axioms union_misses_neuron_aggregate
#print axioms JointState.Neurons.identity_factors
#print axioms JointState.Neurons.shift_not_factors
#print axioms JointState.Neurons.identity_isProductAggregate
#print axioms JointState.Neurons.shift_not_isProductAggregate

end Systems
