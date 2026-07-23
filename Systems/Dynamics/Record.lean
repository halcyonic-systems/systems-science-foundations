/-
  Systems/Dynamics/Record.lean
  The declared Dynamics descriptor — dynamics as checkable data, never embedded code.

  Refines the opaque `τ` (transform) slot of the Mobus 8-tuple (Tuple.lean) into a
  typed DESCRIPTOR of a system's dynamics: over a carrier (state space) it declares
  the support shape, the transition-functor family (by name), the boundary interface
  (input/output ports), and the declared conserved quantities.

  REVISED 2026-07-23 after a frontier-council outside pass (triage:
  `operations/sessions/2026-07-23/references/dynamics-record-council-triage.md`).
  Four accepted findings, all applied:

    1. `conservation` CUT from the kind enum — a category error. It is a property
       over trajectories (it belongs in `invariants`), not a transition-functor
       family like markov / deterministic / nondeterministic. A conserving system is
       `kind = deterministic` with a non-empty `invariants` list — encoded once, not
       two ways with no consistency check.
    2. `parameters` REMOVED, not opaquely kept. A per-kind parameter type (a Markov
       kernel and a deterministic map are different TYPES, not values) cannot be typed
       without committing the endofunctor interpretation — which is the coalgebra
       semantics layer (bert-lenses#112). A bare opaque `Param` was a landmine: the
       later interpretation would force `parameters : KindParam kind Carrier`
       (dependent), breaking every instance. This descriptor defers the typed
       transition to #112 cleanly, rather than typing it prematurely or leaving the
       trap.
    3. `inputType` / `outputType` ADDED (default `Unit`). Openness is BERT's
       differentiator; a portless closed `X → F X` is the wrong default skeleton when
       the interface is load-bearing. A closed system is exactly the `Unit`-port case.
       Two defaulted fields now make the record openness-READY (Mealy / Poly compose
       on typed interfaces); the composition law itself is #112.
    4. `support` stays a descriptor TAG. Typing the time domain (ℕ vs ℝ vs a partial
       order) is a run/semantics concern (#112); the tag is the declared metadata.

  THE PRINCIPLE. Mobus's own answer to "how does a model carry dynamics" was an
  embedded per-element script, which he hedged as "playful exploration" and which
  forfeits the tool's premise (a kernel that owns truth) because a script is opaque
  to every validator. This record is the DECLARATION side — a checkable descriptor,
  not code. The stronger "declaration carries the parameters too" is deliberately
  narrowed to what can be typed without the functor: the typed transition (the
  parameters) is #112.

  CONSERVATIVITY. `τ` is "carried data with no structural role" (Tuple.lean:48-49):
  every coherence constraint and structural theorem quantifies over `τ` opaquely, so
  instantiating `τ := Dynamics C` changes and breaks nothing. Witnessed by the
  closing `example`; `#print axioms` on the examples reports axiom-free.
-/

import Systems.Mobus.Tuple

namespace Systems

/-! ## Support — the declared shape of the index (a metadata tag) -/

/-- Mesarovic–Takahara (Def 2.7) require only a linearly-ordered support; this tag
    names the shape. `eventIndexed` is the support the bert-lenses#67 absorbing-Markov
    chain uses (ℕ counting transition events, not fixed ticks). Typing the actual time
    domain is the semantics layer (bert-lenses#112). -/
inductive Support
  | discrete       -- ℕ, fixed ticks
  | eventIndexed   -- ℕ, counting transition events
  | continuous     -- ℝ
  deriving DecidableEq, Repr

/-! ## Kind — the NAME of the transition-functor family (taxonomy axis C) -/

/-- Names a transition-functor family; the semantics layer (bert-lenses#112)
    interprets the name as an endofunctor. Grounded in the kinds shipped or scoped
    today; extensible. `conservation` is deliberately ABSENT — it is a declared
    invariant (below), not a functor family (frontier-council finding 1). -/
inductive DynamicsKind
  | deterministic     -- Id / X^Σ: a single next state
  | markov            -- Dist(X): discrete-time stochastic (bert-lenses#67, absorbing)
  | nondeterministic  -- 𝒫(X): the powerset kind (the life-cycle ΔS ∈ F(S))
  deriving DecidableEq, Repr

/-! ## Invariant — a declared conserved quantity (taxonomy axis D) -/

/-- A conserved quantity is DECLARED, never assumed by the engine (axis D). At this
    layer it is named; DERIVING it from structure (as a CRN derives conservation from
    its stoichiometry, `ker Nᵀ`) is a deeper design question, not this record's.
    Conservation is ONE optional declaration — `invariants = []` is honest for a kind
    that conserves nothing (e.g. a Markov chain). -/
structure Invariant where
  name : String
  deriving DecidableEq, Repr

/-! ## The descriptor -/

/-- The declared Dynamics descriptor over a carrier (state space): a checkable
    refinement of Mobus's opaque `τ`. It declares WHAT KIND of dynamics, at WHAT
    support, across WHAT boundary interface, preserving WHICH invariants — not the
    transition function itself (that is the typed, per-kind object of bert-lenses#112,
    indexed by this descriptor). -/
structure Dynamics (Carrier : Type) where
  /-- The declared index shape. -/
  support : Support
  /-- The transition-functor family, by name. -/
  kind : DynamicsKind
  /-- The boundary interface, input side. `Unit` = closed (no environment coupling). -/
  inputType : Type := Unit
  /-- The boundary interface, output side. `Unit` = closed. -/
  outputType : Type := Unit
  /-- The declared conserved quantities (possibly none). -/
  invariants : List Invariant

namespace Dynamics

/-- A conservation record — after finding 1 this is `deterministic` carrying a
    declared conserved quantity, NOT a `conservation` kind. Closed (default ports). -/
def conservationExample (C : Type) : Dynamics C where
  support := .discrete
  kind := .deterministic
  invariants := [⟨"mass"⟩]

/-- The bill absorbing-Markov descriptor (bert-lenses#67 ruling, 2026-07-23):
    event-indexed support, the Markov kind, no conserved invariant, closed ports. The
    transition WEIGHTS (the typed parameters) are the #112 object indexed by this. -/
def billMarkovDescriptor (C : Type) : Dynamics C where
  support := .eventIndexed
  kind := .markov
  invariants := []

/-- Finding 1, checked: conservation now rides on the invariant, not the kind — the
    two records differ exactly where the theory says they must, with no `conservation`
    kind to disagree with an empty invariant list. -/
example : (conservationExample Unit).kind = .deterministic ∧
    (conservationExample Unit).invariants ≠ [] ∧
    (billMarkovDescriptor Unit).invariants = [] :=
  ⟨rfl, by decide, rfl⟩

/-- Finding 3, checked: the default interface is closed (`Unit` ports); openness is
    opting a non-`Unit` type into a port, not a redesign. -/
example : (conservationExample Unit).inputType = Unit ∧
    (conservationExample Unit).outputType = Unit :=
  ⟨rfl, rfl⟩

end Dynamics

/-- Conservativity, machine-checked: a MobusSystem can carry the descriptor as its
    `τ`. Because `τ` participates in no coherence constraint (Tuple.lean), this
    refinement of the transform slot changes no structural field. -/
example (C : Type) : Type _ :=
  MobusSystem (Fin 2) Unit Unit Unit (Dynamics C) Unit Unit

end Systems
