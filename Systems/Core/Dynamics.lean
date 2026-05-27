/-
  Systems/Core/Dynamics.lean
  Principle 4: Dynamics — state evolution, equilibrium, coupling, and
  multi-timescale decomposition

  Mobus, Systems Science: Theory, Analysis, Modeling, and Design, Ch. 2:
  "Systems are dynamic on multiple time scales."

  Key definitions:
  - DynamicSystem: ConcreteSystem + deterministic state-transition law
  - CoupledDynamicSystem: mutual influence between subsystems
  - Flow: time-parameterized semigroup action on state space
  - TimescaleDecomposition: fast/slow separation around equilibria

  Key results:
  - Composition: dynamics compose as products, projections preserved
  - Equilibrium: products, coupled fixed points, iteration stability
  - Simon's bridge: InteractionDynamicsBridge completes the conditional
    time-scale separation argument from Level.lean
  - Timescale decomposition: fast dynamics recovers subsystem laws,
    reference equilibrium is fixed point of both fast and slow

  Deferred (research-level, not axiomatization gaps):
  - Quantitative convergence (requires metric on state space)
  - Stochastic and input-dependent transitions
  - Time-varying flows
-/

import Systems.Core.Systemness
import Mathlib.Algebra.Group.Defs

namespace Systems

/-! ## Dynamic System

  A ConcreteSystem paired with a state space and transition law.
  This is the minimal structure that adds dynamics to Bunge's CES triple:
  the system has states, and states change according to a law. -/

/-- A dynamic system: a ConcreteSystem with an associated state space
    and a deterministic state-transition law.

    The law captures "what happens next" — the core content of Dynamics
    (#4) in its simplest form. Richer forms (time-parameterized flows,
    stochastic transitions, input-dependent evolution) extend this;
    the deterministic self-map is the foundation.

    Bunge §2.2: a thing has a state function F mapping time to state.
    The transition law is the generator of this trajectory. -/
structure DynamicSystem (α : Type*) [ActsOn α] (S : Type*) where
  system : ConcreteSystem α
  law : S → S

/-! ## Composition of Dynamics

  When two systems compose (Systemness closure), their dynamics compose
  too. The composed state space is the product S₁ × S₂: each point
  specifies the state of both subsystems.

  This product structure is the formal basis of Simonian complexity:
  if N components each have |S| states, the composed system has |S|^N
  states. Near-decomposability (Hierarchy #2) makes this tractable by
  decomposing the product into modular factors that equilibrate
  independently at fast time scales.

  The independent-evolution law (each subsystem evolves independently)
  is exact for uncoupled systems and approximate for near-decomposable
  systems at the fast time scale. Coupling corrections (the slow
  inter-module dynamics) are Tier 2 territory. -/

/-- Compose two dynamic systems with independent dynamics.

    The composed state space is S₁ × S₂ (product). Each subsystem
    evolves according to its own law, independently.

    This is the "zeroth-order" dynamics of a near-decomposable system:
    at the fast time scale, modules equilibrate independently. The
    coupling corrections (slow inter-module dynamics) are what makes
    near-decomposable systems nearly, not exactly, decomposable. -/
def DynamicSystem.compose {α : Type*} [ActsOn α] {S₁ S₂ : Type*}
    (ds₁ : DynamicSystem α S₁) (ds₂ : DynamicSystem α S₂)
    (h_disjoint : ds₁.system.composition ∩ ds₂.system.composition = ∅)
    (h_interact : ∃ a ∈ ds₁.system.composition,
      ∃ b ∈ ds₂.system.composition, Bonded a b) :
    DynamicSystem α (S₁ × S₂) where
  system := ds₁.system.compose ds₂.system h_disjoint h_interact
  law := fun (s₁, s₂) => (ds₁.law s₁, ds₂.law s₂)

/-- The composed dynamics preserves σ₁'s state evolution:
    projecting the composed state to S₁ and evolving equals
    evolving in S₁ and then projecting. -/
theorem DynamicSystem.compose_proj_left {α : Type*} [ActsOn α]
    {S₁ S₂ : Type*}
    (ds₁ : DynamicSystem α S₁) (ds₂ : DynamicSystem α S₂)
    (h_disjoint : ds₁.system.composition ∩ ds₂.system.composition = ∅)
    (h_interact : ∃ a ∈ ds₁.system.composition,
      ∃ b ∈ ds₂.system.composition, Bonded a b)
    (s : S₁ × S₂) :
    ((ds₁.compose ds₂ h_disjoint h_interact).law s).1 = ds₁.law s.1 := by
  rfl

/-- The composed dynamics preserves σ₂'s state evolution. -/
theorem DynamicSystem.compose_proj_right {α : Type*} [ActsOn α]
    {S₁ S₂ : Type*}
    (ds₁ : DynamicSystem α S₁) (ds₂ : DynamicSystem α S₂)
    (h_disjoint : ds₁.system.composition ∩ ds₂.system.composition = ∅)
    (h_interact : ∃ a ∈ ds₁.system.composition,
      ∃ b ∈ ds₂.system.composition, Bonded a b)
    (s : S₁ × S₂) :
    ((ds₁.compose ds₂ h_disjoint h_interact).law s).2 = ds₂.law s.2 := by
  rfl

/-! ## Interaction-Dynamics Bridge

  Simon's conditional (Level.lean) proves: IF there exists a StrictAnti
  map from interaction strength to time scale, THEN near-decomposability
  implies time-scale separation.

  The bridge structure names this map and its physical meaning: it is the
  claim that a system's dynamics respects its interaction structure.
  Stronger interactions produce faster characteristic dynamics (shorter
  relaxation times). This is the physical content that Dynamics (#4)
  provides to complete Simon's argument.

  The bridge is a STRUCTURE, not a theorem: it names what must be true
  about the dynamics for Simon's implication to hold. Specific dynamical
  laws (linear ODEs, discrete Markov chains, etc.) can be shown to
  satisfy this structure — those are instantiation theorems, each
  connecting a concrete dynamics to the abstract bridge. -/

/-- The interaction-dynamics bridge: stronger interaction produces
    faster characteristic dynamics.

    This is the physical assumption Simon left implicit in his 1962
    paper. It says: interaction strength (a structural property from
    Hierarchy #2) monotonically determines time scale (a dynamical
    property from Dynamics #4).

    `toTimeScale` maps interaction strength to characteristic time.
    `StrictAnti` means stronger interaction → shorter time scale
    (faster dynamics). -/
structure InteractionDynamicsBridge
    (T : Type*) [LinearOrder T]
    (S : Type*) [Preorder S] where
  toTimeScale : T → S
  strictAnti : StrictAnti toTimeScale

/-- Simon's conditional, instantiated from a dynamics-interaction bridge.

    Given a near-decomposable system and evidence that its dynamics
    respects its interaction structure, within-module dynamics are
    strictly faster than between-module dynamics.

    This is the COMPLETED form of Simon's argument: the conditional
    from Level.lean supplies the logic; the bridge supplies the
    dynamical assumption. Together they prove time-scale separation. -/
theorem NearDecomposable.simon_from_bridge
    {α : Type*} [ActsOn α]
    {σ : ConcreteSystem α} {T : Type*} [LinearOrder T]
    [InteractionStrength α T]
    (nd : NearDecomposable σ T)
    {S : Type*} [Preorder S]
    (bridge : InteractionDynamicsBridge T S)
    {m₁ m₂ : Set α} (hm₁ : m₁ ∈ nd.modules) (hm₂ : m₂ ∈ nd.modules)
    (hne : m₁ ≠ m₂)
    {a b : α} (ha : a ∈ m₁) (hb : b ∈ m₁) (hab : a ≠ b)
    {c : α} (hc : c ∈ m₂) :
    bridge.toTimeScale (@strength α T _ a b) <
      bridge.toTimeScale (@strength α T _ a c) :=
  nd.conditional_time_scale_separation bridge.toTimeScale bridge.strictAnti
    hm₁ hm₂ hne ha hb hab hc

/-! ## Equilibrium

  A fixed point of the dynamics: a state where the law maps s to itself.
  Defined early because both independent and coupled dynamics reference it. -/

/-- A state is an equilibrium of a transition law if the law leaves it fixed. -/
def IsEquilibrium {S : Type*} (f : S → S) (s : S) : Prop := f s = s

/-! ## Multi-Step Evolution and Trajectories

  A DynamicSystem.law is one step. Iteration gives multi-step evolution.
  The trajectory (sequence of states over time) connects to State.lean's
  history type: the law is the GENERATOR; the trajectory is what
  State.lean's history records. -/

/-- Evolve a dynamic system's state by n steps of the transition law. -/
def DynamicSystem.evolve {α : Type*} [ActsOn α] {S : Type*}
    (ds : DynamicSystem α S) (n : ℕ) (s : S) : S :=
  ds.law^[n] s

/-- The trajectory of a dynamic system from an initial state:
    the sequence of states visited at each time step.
    This is the discrete analogue of State.lean's `history`. -/
def DynamicSystem.trajectory {α : Type*} [ActsOn α] {S : Type*}
    (ds : DynamicSystem α S) (s₀ : S) (times : Set ℕ) : Set (ℕ × S) :=
  {p | p.1 ∈ times ∧ ds.evolve p.1 s₀ = p.2}

/-! ## Coupled Dynamics

  DynamicSystem.compose assumes independent evolution: each subsystem
  ignores the other's state. CoupledDynamicSystem captures the general
  case: each subsystem's law depends on the other's state.

  Near-decomposable systems (Hierarchy #2) are weakly coupled: the
  coupling terms are small relative to the independent terms.
  Independent dynamics (DynamicSystem.compose) is the zeroth-order
  approximation; the coupling corrections are the first-order. -/

/-- A coupled dynamic system: two subsystems whose evolution depends
    on each other's state.

    `law₁ s₁ s₂` gives the next state of subsystem 1 given both
    subsystems' current states. Similarly for `law₂`.

    Independent dynamics is the special case where law₁ ignores s₂
    and law₂ ignores s₁. -/
structure CoupledDynamicSystem (α : Type*) [ActsOn α]
    (S₁ : Type*) (S₂ : Type*) where
  system : ConcreteSystem α
  law₁ : S₁ → S₂ → S₁
  law₂ : S₁ → S₂ → S₂

/-- The combined law of a coupled system on the product state space. -/
def CoupledDynamicSystem.combinedLaw {α : Type*} [ActsOn α]
    {S₁ S₂ : Type*} (cds : CoupledDynamicSystem α S₁ S₂) :
    S₁ × S₂ → S₁ × S₂ :=
  fun (s₁, s₂) => (cds.law₁ s₁ s₂, cds.law₂ s₁ s₂)

/-- An independent DynamicSystem.compose is a special case of coupled
    dynamics where each law ignores the other subsystem's state. -/
def DynamicSystem.toCoupled {α : Type*} [ActsOn α] {S₁ S₂ : Type*}
    (ds₁ : DynamicSystem α S₁) (ds₂ : DynamicSystem α S₂)
    (h_disjoint : ds₁.system.composition ∩ ds₂.system.composition = ∅)
    (h_interact : ∃ a ∈ ds₁.system.composition,
      ∃ b ∈ ds₂.system.composition, Bonded a b) :
    CoupledDynamicSystem α S₁ S₂ where
  system := ds₁.system.compose ds₂.system h_disjoint h_interact
  law₁ := fun s₁ _ => ds₁.law s₁
  law₂ := fun _ s₂ => ds₂.law s₂

/-- A coupled equilibrium: a state where both subsystems are fixed
    given each other's state. -/
def CoupledEquilibrium {S₁ S₂ : Type*}
    (law₁ : S₁ → S₂ → S₁) (law₂ : S₁ → S₂ → S₂)
    (s₁ : S₁) (s₂ : S₂) : Prop :=
  law₁ s₁ s₂ = s₁ ∧ law₂ s₁ s₂ = s₂

/-- A coupled equilibrium is a fixed point of the combined law. -/
theorem coupled_equilibrium_iff_fixed {α : Type*} [ActsOn α] {S₁ S₂ : Type*}
    {cds : CoupledDynamicSystem α S₁ S₂}
    {s₁ : S₁} {s₂ : S₂} :
    CoupledEquilibrium cds.law₁ cds.law₂ s₁ s₂ ↔
      IsEquilibrium cds.combinedLaw (s₁, s₂) := by
  constructor
  · intro ⟨h₁, h₂⟩
    unfold IsEquilibrium CoupledDynamicSystem.combinedLaw
    simp [h₁, h₂]
  · intro h
    unfold IsEquilibrium CoupledDynamicSystem.combinedLaw at h
    exact ⟨congr_arg Prod.fst h, congr_arg Prod.snd h⟩

/-- Independent equilibria are coupled equilibria: if each subsystem
    is at equilibrium independently, they're at coupled equilibrium
    for independent dynamics. -/
theorem independent_equilibrium_is_coupled {α : Type*} [ActsOn α]
    {S₁ S₂ : Type*}
    {ds₁ : DynamicSystem α S₁} {ds₂ : DynamicSystem α S₂}
    {s₁ : S₁} {s₂ : S₂}
    (h_disjoint : ds₁.system.composition ∩ ds₂.system.composition = ∅)
    (h_interact : ∃ a ∈ ds₁.system.composition,
      ∃ b ∈ ds₂.system.composition, Bonded a b)
    (h₁ : IsEquilibrium ds₁.law s₁)
    (h₂ : IsEquilibrium ds₂.law s₂) :
    CoupledEquilibrium
      (ds₁.toCoupled ds₂ h_disjoint h_interact).law₁
      (ds₁.toCoupled ds₂ h_disjoint h_interact).law₂ s₁ s₂ :=
  ⟨h₁, h₂⟩

/-! ## Product Equilibrium and Iteration -/

/-- Product equilibrium: if s₁ is equilibrium of law₁ and s₂ of law₂,
    then (s₁, s₂) is equilibrium of the composed (product) law.

    This connects to DynamicSystem.compose: equilibria of composed
    systems are products of subsystem equilibria — exactly when
    subsystems are decoupled (independent dynamics). -/
theorem product_equilibrium {S₁ S₂ : Type*}
    {f₁ : S₁ → S₁} {f₂ : S₂ → S₂}
    {s₁ : S₁} {s₂ : S₂}
    (h₁ : IsEquilibrium f₁ s₁) (h₂ : IsEquilibrium f₂ s₂) :
    IsEquilibrium (fun (p : S₁ × S₂) => (f₁ p.1, f₂ p.2)) (s₁, s₂) := by
  unfold IsEquilibrium at *
  simp [h₁, h₂]

/-- An equilibrium is preserved under iteration: if f(s) = s then
    f^[n](s) = s for all n. The trajectory from equilibrium is constant. -/
theorem equilibrium_iterate {S : Type*} {f : S → S} {s : S}
    (h : IsEquilibrium f s) (n : ℕ) :
    f^[n] s = s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply, ih]
    exact h

/-! ## Flow (Time-Parameterized Dynamics)

  A flow is a one-parameter semigroup action on state space: the
  algebraic structure of deterministic time-parameterized dynamics.
  DynamicSystem.law is a single discrete step; Flow generalizes to
  arbitrary time types with additive structure. -/

/-- A deterministic flow: a one-parameter semigroup action on state space.

    `flow t s` is the state reached from s after elapsed time t.
    The two axioms capture determinism:
    - `flow_zero`: no time elapsed → no change
    - `flow_add`: flowing for t₁ then t₂ equals flowing for t₁ + t₂ -/
structure Flow (S : Type*) (T : Type*) [AddMonoid T] where
  flow : T → S → S
  flow_zero : ∀ s, flow 0 s = s
  flow_add : ∀ t₁ t₂ s, flow (t₁ + t₂) s = flow t₁ (flow t₂ s)

/-- An equilibrium of a flow is fixed at all times. -/
theorem Flow.equilibrium_fixed {S T : Type*} [AddMonoid T]
    (f : Flow S T) {s : S} (h : ∀ t, f.flow t s = s) (t : T) :
    f.flow t s = s :=
  h t

/-- A flow generates a trajectory from an initial state.
    Connects to State.lean's `history` type: the flow is the GENERATOR;
    the trajectory is what history records. -/
def Flow.trajectory {S T : Type*} [AddMonoid T]
    (f : Flow S T) (s₀ : S) (times : Set T) : Set (T × S) :=
  {p | p.1 ∈ times ∧ f.flow p.1 s₀ = p.2}

/-- Compose two flows with independent dynamics on a product state space. -/
def Flow.compose {S₁ S₂ T : Type*} [AddMonoid T]
    (f₁ : Flow S₁ T) (f₂ : Flow S₂ T) : Flow (S₁ × S₂) T where
  flow := fun t (s₁, s₂) => (f₁.flow t s₁, f₂.flow t s₂)
  flow_zero := by
    intro ⟨s₁, s₂⟩
    simp [f₁.flow_zero, f₂.flow_zero]
  flow_add := by
    intro t₁ t₂ ⟨s₁, s₂⟩
    simp [f₁.flow_add, f₂.flow_add]

/-- Composed flow projects to subsystem 1. -/
theorem Flow.compose_proj_left {S₁ S₂ T : Type*} [AddMonoid T]
    (f₁ : Flow S₁ T) (f₂ : Flow S₂ T)
    (t : T) (s : S₁ × S₂) :
    ((f₁.compose f₂).flow t s).1 = f₁.flow t s.1 := by
  rfl

/-- Composed flow projects to subsystem 2. -/
theorem Flow.compose_proj_right {S₁ S₂ T : Type*} [AddMonoid T]
    (f₁ : Flow S₁ T) (f₂ : Flow S₂ T)
    (t : T) (s : S₁ × S₂) :
    ((f₁.compose f₂).flow t s).2 = f₂.flow t s.2 := by
  rfl

/-! ## Timescale Decomposition

  The structural skeleton of Simon's multi-timescale argument.

  Given a coupled system and a reference equilibrium, the dynamics
  decomposes into FAST (within-module: freeze the other subsystem at
  equilibrium, evolve independently) and SLOW (between-module: the full
  coupled evolution including coupling corrections).

  Key structural result: the fast dynamics' fixed points ARE the product
  equilibria. This is why near-decomposable systems exhibit time-scale
  separation — the fast dynamics converges to product equilibria first,
  then the slow coupling dynamics moves the system along the equilibrium
  manifold.

  The QUANTITATIVE result (fast converges, slow is well-approximated
  by restriction to the equilibrium manifold) requires a metric on
  state space and is deferred to a future session. The STRUCTURAL
  skeleton is the contribution here. -/

/-- A timescale decomposition of coupled dynamics into fast and slow parts.

    - `fast₁` / `fast₂`: within-module dynamics (each subsystem evolves
      with the other frozen at equilibrium)
    - `slow`: the full coupled dynamics on the product space

    Simon's insight: in near-decomposable systems, the fast dynamics
    reaches equilibrium quickly (within-module interactions are strong),
    then the slow dynamics operates on the manifold of fast equilibria
    (between-module interactions are weak). -/
structure TimescaleDecomposition (S₁ : Type*) (S₂ : Type*) where
  fast₁ : S₁ → S₁
  fast₂ : S₂ → S₂
  slow : S₁ × S₂ → S₁ × S₂

/-- Decompose a coupled dynamic system into fast and slow components
    around a reference equilibrium.

    The fast dynamics freezes the other subsystem at its equilibrium
    value and evolves independently. The slow dynamics is the full
    coupled evolution.

    This construction requires a coupled equilibrium as the reference
    point — the "operating point" around which the decomposition is
    defined. Different equilibria give different decompositions. -/
def CoupledDynamicSystem.decompose {α : Type*} [ActsOn α]
    {S₁ S₂ : Type*} (cds : CoupledDynamicSystem α S₁ S₂)
    (eq₁ : S₁) (eq₂ : S₂)
    (_h_eq : CoupledEquilibrium cds.law₁ cds.law₂ eq₁ eq₂) :
    TimescaleDecomposition S₁ S₂ where
  fast₁ := fun s₁ => cds.law₁ s₁ eq₂
  fast₂ := fun s₂ => cds.law₂ eq₁ s₂
  slow := cds.combinedLaw

/-- The reference equilibrium is a fixed point of the fast dynamics.

    This is the structural content of "product equilibria are fast
    equilibria": each subsystem is at rest when the other is frozen
    at equilibrium. The fast dynamics converges TO this state. -/
theorem CoupledDynamicSystem.decompose_fast₁_equilibrium
    {α : Type*} [ActsOn α] {S₁ S₂ : Type*}
    (cds : CoupledDynamicSystem α S₁ S₂)
    {eq₁ : S₁} {eq₂ : S₂}
    (h_eq : CoupledEquilibrium cds.law₁ cds.law₂ eq₁ eq₂) :
    IsEquilibrium (cds.decompose eq₁ eq₂ h_eq).fast₁ eq₁ :=
  h_eq.1

/-- The reference equilibrium is a fixed point of fast₂. -/
theorem CoupledDynamicSystem.decompose_fast₂_equilibrium
    {α : Type*} [ActsOn α] {S₁ S₂ : Type*}
    (cds : CoupledDynamicSystem α S₁ S₂)
    {eq₁ : S₁} {eq₂ : S₂}
    (h_eq : CoupledEquilibrium cds.law₁ cds.law₂ eq₁ eq₂) :
    IsEquilibrium (cds.decompose eq₁ eq₂ h_eq).fast₂ eq₂ :=
  h_eq.2

/-- The slow dynamics at the fast equilibrium is stationary.
    At the reference equilibrium, neither fast nor slow dynamics
    moves the system — it's a fixed point of the full evolution. -/
theorem CoupledDynamicSystem.decompose_slow_at_equilibrium
    {α : Type*} [ActsOn α] {S₁ S₂ : Type*}
    (cds : CoupledDynamicSystem α S₁ S₂)
    {eq₁ : S₁} {eq₂ : S₂}
    (h_eq : CoupledEquilibrium cds.law₁ cds.law₂ eq₁ eq₂) :
    IsEquilibrium (cds.decompose eq₁ eq₂ h_eq).slow (eq₁, eq₂) :=
  (coupled_equilibrium_iff_fixed.mp h_eq : IsEquilibrium cds.combinedLaw (eq₁, eq₂))

/-- For independent dynamics, the decomposition's fast laws recover
    the original subsystem laws exactly.

    This is the "zero coupling" case: when the laws don't depend on
    each other's state, the fast dynamics IS the full dynamics, and
    the decomposition is trivial. -/
theorem decompose_independent_fast₁ {α : Type*} [ActsOn α]
    {S₁ S₂ : Type*}
    {ds₁ : DynamicSystem α S₁} {ds₂ : DynamicSystem α S₂}
    {s₁ : S₁} {s₂ : S₂}
    (h_disjoint : ds₁.system.composition ∩ ds₂.system.composition = ∅)
    (h_interact : ∃ a ∈ ds₁.system.composition,
      ∃ b ∈ ds₂.system.composition, Bonded a b)
    (h₁ : IsEquilibrium ds₁.law s₁)
    (h₂ : IsEquilibrium ds₂.law s₂) :
    (ds₁.toCoupled ds₂ h_disjoint h_interact |>.decompose s₁ s₂
      (independent_equilibrium_is_coupled h_disjoint h_interact h₁ h₂)).fast₁ = ds₁.law :=
  rfl

/-- For independent dynamics, fast₂ recovers the original law₂. -/
theorem decompose_independent_fast₂ {α : Type*} [ActsOn α]
    {S₁ S₂ : Type*}
    {ds₁ : DynamicSystem α S₁} {ds₂ : DynamicSystem α S₂}
    {s₁ : S₁} {s₂ : S₂}
    (h_disjoint : ds₁.system.composition ∩ ds₂.system.composition = ∅)
    (h_interact : ∃ a ∈ ds₁.system.composition,
      ∃ b ∈ ds₂.system.composition, Bonded a b)
    (h₁ : IsEquilibrium ds₁.law s₁)
    (h₂ : IsEquilibrium ds₂.law s₂) :
    (ds₁.toCoupled ds₂ h_disjoint h_interact |>.decompose s₁ s₂
      (independent_equilibrium_is_coupled h_disjoint h_interact h₁ h₂)).fast₂ = ds₂.law :=
  rfl

end Systems
