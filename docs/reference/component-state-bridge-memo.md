# The component–state bridge

*Read-only research memo, 2026-09-04. Every claim carries a file:line; nothing here was edited or committed.*

Path prefixes: SSF = `~/Desktop/halcyonic-projects/active/systems-science-foundations`; V = `~/Desktop/halcyonic/operations/systems-science`; LC = `~/Desktop/halcyonic-projects/active/mobus-lifecycle-paper`; BC = `~/Desktop/halcyonic-projects/active/bert/bert-compose`; FD = `~/Desktop/halcyonic-projects/active/facets/docs/design`.

## Question

What is the first-principles relation between a system's components and its state, across the sources this program holds, and which sources state it with conviction?

## Verdict on the hypothesis

The hypothesis holds, with one amendment. Every mathematical tradition held here (Klir, Mesarovic, Wymore, Myers, and Bunge's own worked examples) defines a system's state as a point in a product indexed by variables, ports, or components, with composition as product plus a coupling constraint. Bunge's "union" at 1979 p. 640 is real text, not a misreading, but it is contradicted by his own worked example in the 1977 volume, by his own Fig. 1.5 caption in 1979, and by his 1977 definition, all of which are product-shaped. The amendment: Mobus's flows are not additional independent coordinates in the wiring traditions; Willems treats them as shared variables and Myers as wires, so flow readings are derived from, or constrained by, component states rather than free axes.

## (A) Each source's position

**Mobus 2022 (conviction: high, but informal).** State is a reading over all dynamical elements at one tick with structure fixed: "Imagine taking a reading on every flow (connection) and every reservoir in a system and all of its subsystems every Δt instance. The state, σ_i, of the system where, i, is the index of the set of possible states, S, and σ_i is an element of that set" (V/mobus/4-a-model-of-system.md:460). The next sentence supplies the lawful-subset idea: "Since by definition a system is an organized set of parts (components and subcomponents) the number of possible states is constrained" (:461). H is the time series of such readings: "Let H at time t be defined as a set of measures (a list of variables in the system), H_t = [v_1, v_2, ..., v_n]_t" and "The time series of H_t sets provide a set of snapshots of the state of S at each time increment" (:423-428). T is per component: "for each c_{i,l} ∈ C_{i,l} there is a formula, equation, or algorithm, t_{i,l}, that describes the transfer function of that component" (:407). The 2022 text defines the 7-tuple at :196-198. Chapters 3, 10 and 12 add no definition of state (only incidental uses, e.g. 3-system-ontology.md:598, 10-model-archetypes.md:122). Mobus-Kalton 2015 holds only an incidental mention: "the state of the system is recorded in a file, H" (V/mobus-kalton-2015/10-auto-organization-and-emergence.md:2690).

**Bunge (conviction: high, internally inconsistent).** State function F = ⟨F_1, ..., F_n⟩, one coordinate per property: "The components F_i of the list F of functions in a functional schema are usually called state variables because their values contribute to characterizing or identifying the states the thing of interest can be in" (V/bunge/Bunge - 1977 - Ontology I - The Furniture of the World.md:6491-6493). The lawful state space "is a subset of the cartesian product of the ranges of the components of the state function" (V/bunge/Bunge - 1979 - Treatise on Basic Philosophy.md:649, Fig. 1.5 caption). The aggregate example is a product: "If the neurons are regarded as mutually independent, the state space of the aggregate [N] of neurons (i.e. the system of interest) is S([N]) = {0,1}^|N|. Thus for a system composed of 3 neurons, the state space has 2^3 elements" (1977:6794-6796). Yet p. 640 says: "we may take the total state space to equal the union of the partial state spaces. In particular, let S_L(K) and S_L(M) be the lawful states spaces of things of kinds K and M respectively. Then the state space of the association k+m of two noninteracting things of kinds K and M respectively, relative to the same reference frame, is S_L(K) ∪ S_L(M). Not so in the case of a system: here the state of every component is determined, at least partly, by the states other system components are in, so that the total state space is no longer the union of the partial state spaces" (1979:650). The 1977 definition is stated on histories, not state spaces: "X is an aggregate (or conglomerate or heap) iff, in every representation of X (i.e. for every choice of state function), its history h(X) equals the union of the partial histories h(X_i). Otherwise X is a system" (1977:13062-13064). The system case is argued by Pauli: "The Pauli principle expresses a global or systemic property, one that the individual components fail to possess, whence it cannot be represented in the partial state spaces. Therefore the construction of the state space of the system must proceed from scratch rather than on the sole basis of the state spaces of the individual electrons" (1977:13051-13056). The 1979 coupling-matrix passage says the same in product form: "If the off-diagonal coefficients vanish or are very small compared with the diagonal elements, then each component evolves separately or nearly so and, instead of a system proper, we have just an aggregate. Otherwise the evolutions of the system components are coupled" (1979:4488). The bond criterion follows at 1977:13081-13082: "X is a system iff the bondage of C(X) is not empty."

**Klir (conviction: high).** "systems are then conceived as sets of variables together with a relation recognized among their state sets" (V/klir/klir-facets.md:3533-3534); each variable has "a particular set of entities through which it manifests itself. These entities are usually referred to as states (or values) of the variable; the whole set is called a state set" (:3524-3526); data are functions whose range is "the set of overall states of the basic variables" (:3894); the state-transition form is "z' = g(x, z)" (:1350).

**Mesarovic and Takahara 1975 (conviction: high).** "Definition 1.1. A (general) system is a relation on nonempty (abstract) sets S ⊂ ×{V_i : i ∈ I}" (V/mesarovic/mesarovic-takahara-1975-ch2.md:37-38); state is a derived object: "C is then a global state object or set, its elements being global states, while R is a global (systems)-response function" with R : C × X → Y (:270); "Theorem 1.1. Every system has a global-response function" (:271). SSF records the 1964 side: the state "embodies the entire past history" and Z := A × B is that prefix history (SSF/Systems/Mesarovic/Decomposition.lean:31-38).

**Wymore 1993 (conviction: high).** "in which a system has multiple state variables. In such a case, the state of the system requires more than one quantity or value for its description, which is the same as the case in which each state is represented or modeled by a vector" (V/wymore/wymore-1993-mbse-ch2-systems.md:501); SFZ is the list of Cartesian factor sets of SZ (:503-505); Theorem 2.78 builds a new system whose state is "an n + m dimensional vector whose first n coordinates are elements of the n original output ports, respectively, and the last m coordinates are elements of the original state factor sets" (:561-563). State depends on input history and initial state (:176).

**Willems (conviction: high, dissenting on the status of state).** State variables are latent auxiliaries: "State variables are examples of the usefulness of latent variables in general dynamical models. Input/state/output models, such as (17), have the special feature that they specify the relation between inputs and outputs through a set of auxiliary variables, the state variables" (V/willems/willems-2007-behavioral-approach.md:701-705). Interconnection is variable sharing: "After interconnection, the two hydraulic systems share the pressure and flow variables" (:57); "Interconnection is variable sharing" (:322). SSF already records this: "Willems has no state object: the behavioral point is that state is a latent variable of a representation" (SSF/Systems/Category/ShapeWillems.lean:74-76).

**Myers (conviction: high; the categorical answer).** A deterministic system has "a set State_S of states", "a function expose_S : State_S → Out_S", "a function update_S : State_S × In_S → State_S" (V/myers/myers-categorical-systems-theory.md:936-946), interpretable "in any cartesian category C" (:955). The parallel product: "State_{S1⊗S2} := State_{S1} × State_{S2}" with coordinatewise expose and update (:2190-2194). Wiring couples: "We are setting the parameters of the systems of Rabbits and Foxes according to the states of the other system" (:1369-1370). Composite behaviors are recoverable from parts only under a condition: "while behaviors of component systems will induce behaviors of composite systems, it isn't necessarily the case that all behaviors of the composite arise this way... we ask that T expose its entire state, which is to say that expose_T is an isomorphism" (:23544-23550, Theorem 5.3.3.1 at :23552).

**Spivak (via SSF docs).** State is a role fixed by the integrator, "the choice of stored state (S := Q vs S := T*Q)" (SSF/docs/reference/spivak-adaptive-arrangements.md:50); the SSF encoding casts "the dependency cast in the state role" (SSF/Systems/Klir/SpivakSystem.lean:65). The 2014 book in the vault defines products of sets (V/spivak/category-theory-sciences-full.md:1095) and discrete dynamical systems (:4278-4286) but no composite-state rule.

**bert-compose (conviction: high; empirical).** "Buffering is a conservative stock — the system's state/memory lives there" (BC/src/circuit.rs:8); "Each tick reads the previous tick's wire amounts and writes the next" (:10-11); the recorded row is "[tick, n0.activity, n0.storage, n0.total, n1…]" and is "Cleared on Reset or when the topology changes mid-recording" (:422-424). Node state is `storage` (:306); the reservoir is "the ONLY primitive that carries state" (BC/src/docs.rs:48). The run state is therefore a product over nodes of storage plus wire amounts, indexed by the current topology.

**Facets dynamics docs.** Agent trajectories carry "∏ᵢ agent states" and multi-timescale hierarchy a "product over levels" (FD/dynamics-principled-position.md:183-184); the one worked composite runs over "the product state Sc × Sp" (FD/dynamics-halfb-open-composition.md:232-233); the lifecycle state space is "the set of coherent 8-tuples" (FD/mobus-lifecycle-formalization.md:117); "The phase must be carried, not computed: PhasedSystem := MobusSystem × Fin 5" (:129); bert-compose's history clearing on topology change is read as "a flat refutation of structure-as-more-state" (:137-147).

**Lifecycle paper.** "X = set of ALL oct-tuples over chosen carriers = state space. S ∈ X = one oct-tuple = one complete description at one moment" (LC/scaffold.md:96-97); "A change operator is a partial function δ : X ⇀ X" (LC/paper.tex:216-220); trajectories satisfy S_{t+1} ∈ F(S_t) (:228-233, :239-252).

**SSF today.** `DynamicSystem` carries `system : ConcreteSystem α` and `law : S → S` with no map between α and S (SSF/Systems/Core/Dynamics.lean:50-52). `ConcreteSystem` holds `composition : Set α` and `structure' : Set (α × α)` (SSF/Systems/Core/System.lean:47-53). The binary product with coupling already exists as `CoupledDynamicSystem` with `law₁ : S₁ → S₂ → S₁` and `law₂ : S₁ → S₂ → S₂` (Dynamics.lean:230-240). The union criterion is encoded as a fold over `List (Set S)` on one shared carrier (SSF/Systems/Core/State.lean:114-116) and re-encoded as an indexed union `c.totalSpace = ⋃ x ∈ c.things, c.stateOf x` (SSF/Systems/Bunge/AggregateBridge.lean:93-94), with the coupling postulates named but not asserted (:145-161). The N-fold product is requested and unbuilt: "S^N reduces to modular products" (SSF/Systems/Core/Complexity.lean:167-172). `MobusSystem` carries T, H, Δt as opaque parameters with "no structural role in the ontology" (SSF/Systems/Mobus/Tuple.lean:47-49, :76-82). The Wymore comparison functor maps "state ↦ components" (SSF/Systems/Category/ShapeWymore.lean:49-51). The reference docs contain no state definition beyond Bunge's CES quote (SSF/docs/reference/mobus-bunge-system-definitions-reference.md:185); `RecursiveComponent` has "no state change" (SSF/docs/reference/recursive-component-architecture.md:38). GSR docs contain no state definition (grep of `general-systems-reasoner/docs` returned nothing).

## (B) Comparison table

| Source | Carrier of one state | Composite state | Aggregate test | Flows |
|---|---|---|---|---|
| Mobus 2022 (4-a-model:460) | reading over reservoirs and flows | implicit product, structure fixed | none; states "constrained" (:461) | coordinates |
| Bunge 1977 (:6494, :13062) | n-tuple of property values | product (neurons: 2^N, :6795) | history of whole = union of histories | not modeled |
| Bunge 1979 (:649-650) | same | "union" of partial spaces (:650); product in Fig. 1.5 (:649) | joint space = union | not modeled |
| Klir (:3533) | overall state of variables | product of state sets | none | variables |
| Mesarovic (:37-38) | global state object | relation on a product | noninteractive decomposition | objects V_i |
| Wymore (:501-505) | vector of state factors | product of factors (:561) | none | ports |
| Willems (:702, :57) | latent variable | shared variables | none | shared variables |
| Myers (:936, :2190) | State_S | State_1 × State_2, wiring couples | expose iso for tautness (:23549) | wires |
| bert-compose (circuit.rs:8-11, :422) | storage per node + wire amounts | product indexed by topology | n/a | wire amounts |
| Lifecycle paper (scaffold:96) | the 8-tuple itself | n/a | n/a | inside the tuple |
| SSF now (Dynamics.lean:50, State.lean:114) | opaque S | S₁ × S₂ | union over shared S | none |

## (C) Recommended SSF encoding

All three positions can be kept, because they live at two levels. The tuple is not the run state; it is the index of the run state. Encode a dependent product:

```lean
structure StateCarrier (α : Type*) [ActsOn α] where
  system : ConcreteSystem α
  Q : α → Type*          -- per-component state set (Klir/Bunge/Wymore factor)
  K : α × α → Type*      -- per-flow reading (Mobus flows; Unit when unmodeled)

def JointState (c : StateCarrier α) : Type* :=
  ((a : {a // a ∈ c.system.composition}) → c.Q a) ×
  ((e : {e // e ∈ c.system.structure'}) → c.K e)

structure LawfulDynamics (c : StateCarrier α) where
  lawful : Set (JointState c)   -- Bunge S_L ⊆ product (1979:649)
  law : JointState c → JointState c
  closed : ∀ s ∈ lawful, law s ∈ lawful

def Factors (c : StateCarrier α) (law : JointState c → JointState c) : Prop :=
  ∀ a, ∃ f : c.Q a → c.Q a, ∀ s, (law s).1 a = f (s.1 a)
```

Faithfulness. Mobus 4-a-model:460 is literally a product over reservoirs (component coordinates) and flows (edge coordinates) at fixed structure; `K` is the flow coordinate and `Q` the reservoir coordinate. Bunge's lawful subset (1979:649) is `lawful`. The lifecycle paper is unchanged: its X indexes `StateCarrier`, and a lifecycle step re-indexes `JointState`, which is exactly what circuit.rs:422-424 does when it clears history on topology change, and what FD/mobus-lifecycle-formalization.md:137-147 already argues. `CoupledDynamicSystem` (Dynamics.lean:230-240) becomes the two-component instance; `DynamicSystem.compose` (Dynamics.lean:99-107) becomes the instance where `Factors` holds. The aggregate criterion is restated as `Factors law` together with `lawful = univ`, following Bunge 1979:4488, rather than as set-equality with a union. AggregateBridge's two witnesses (AggregateBridge.lean:101-128) survive by rebuilding on `Factors`; the independence verdict (:132-143) is unchanged in form.

## (D) Smallest separating theorem

Bunge's own three-neuron aggregate (1977:6795-6796) refutes the union encoding. For any three embeddings e_i : Bool → (Fin 3 → Bool), the union of their images has at most 6 points, while the product has 8, so `isAggregate` at State.lean:114-116 (and `stateAggregate` at AggregateBridge.lean:93-94) classifies Bunge's paradigm aggregate as a system.

```lean
theorem union_misses_neuron_aggregate
    (e : Fin 3 → Bool → (Fin 3 → Bool)) :
    (⋃ i, Set.range (e i)) ≠ Set.univ
```

Proof by cardinality: `Fintype.card (Fin 3 → Bool) = 8`, each range has at most 2 elements, three ranges cover at most 6. Companion positive instances on the same carrier with `Q := fun _ => Bool`, `K := fun _ => Unit`: `law := id` satisfies `Factors` (the aggregate), and `law := fun s => (fun a => s.1 (a + 1), s.2)` does not (the system). Nothing weaker separates the two encodings, because on a one-component carrier product and union coincide, which is exactly the vacuity AggregateBridge.lean:57-59 already excludes.

## (E) Open questions for the author

1. Bunge's word "union" at 1979:650 is unambiguous. Decide whether to cite it as a slip corrected by his own 1977:6795 and Fig. 1.5 (1979:649), or to treat 1977 Def 5.35 on histories (1977:13062-13064) as the authoritative form and derive the product reading from it. The showcase comment at State.lean:13-14 and :106-108 currently repeats the union wording.
2. Mobus makes flow readings state coordinates (4-a-model:460); Willems (:57, :322) and Myers (:1369) make them shared or wired variables constrained by component states. Decide whether `K` is a free axis or a derived function of `Q` values at the endpoints. bert-compose keeps wire amounts as one-tick-lag state (circuit.rs:10-11), which supports the free-axis reading.
3. Cor 5.14's bond–state coupling stays a named hypothesis (AggregateBridge.lean:145-161) unless `ActsOn` is redefined as "coordinate b's successor depends on coordinate a", which would make `couplingForward` definitional and `couplingBackward` a no-conspiracy postulate.
4. H sits inside the tuple in the lifecycle paper (scaffold.md:96-97) but is a time series over the run state in Mobus (4-a-model:423-428). Under the dependent encoding H's type changes whenever the index changes; the paper should say so, and FD/mobus-lifecycle-formalization.md:129 ("carried, not computed") already points that way.
5. Myers's tautness condition, `expose` an isomorphism (:23549-23553), is the categorical form of "whole equals composite of parts". Whether it coincides with Bunge's aggregate criterion under the product encoding is a theorem nobody has stated.
6. Whether `lawful` should be a subset (Bunge) or a relation on the product with state derived (Mesarovic :37-38, :270). The two agree for closed systems and differ once inputs enter, which `DynamicSystem.law` (Dynamics.lean:52) currently excludes.
