/-
  Systems/Dynamics/Record.lean
  The declared Dynamics record — dynamics as checkable data, never embedded code.

  Refines the opaque `τ` (transform) slot of the Mobus 8-tuple (Tuple.lean) into
  the five-field record the SL spec pre-designs (bert-lenses `docs/language/spec.md`
  §8.2, adopted): support · carrier · kind · invariants · parameters.

  THE PRINCIPLE. Mobus's own answer to "how does a model carry dynamics" was an
  embedded script per element (§4.4.1.2.3), which he framed as "playful
  exploration". A script is opaque to every validator, so it forfeits the tool's
  premise — a kernel that owns truth. Declaration subsumes it: everything a
  per-element script legitimately expresses is nameable data — a transfer-function
  family (the `kind`) plus its `parameters`, a conserved `invariant`, a `support`.
  An engine interprets the declaration and is verified ONCE against the semigroup
  contract, not per model. The `kind` is a functor family (checkable); the
  invariants are declared (checkable).

  LAYER. This is the DECLARATION layer: typed vocabulary, standing on thoroughly
  solved prior art (DEVS's model-as-tuple + verified abstract simulator; CRN's
  name-the-kind + derived invariants; Modelica's declared equations). Interpreting
  a `kind` as an actual endofunctor X → F(X), and composing OPEN systems across a
  boundary, is the coalgebra semantics layer (bert-lenses#112) — deliberately
  downstream, and the one genuinely-frontier piece (Rutten's coalgebras are closed;
  openness arrives via Poly / structured cospans / Mealy).

  CONSERVATIVITY. `τ` is "carried data with no structural role in the ontology"
  (Tuple.lean:48-49): every coherence constraint and every structural theorem of
  MobusSystem quantifies over `τ` opaquely. Instantiating `τ := Dynamics C P`
  therefore cannot change or break any existing result — this file only ADDS. The
  `example` at the end machine-checks that a MobusSystem can carry the record.
-/

import Systems.Mobus.Tuple

namespace Systems

/-! ## Support — the shape of the index a dynamics is read against -/

/-- Mesarovic–Takahara (Def 2.7) require only a linearly-ordered support; these
    are the concrete shapes the tool declares. `eventIndexed` is the support the
    bert-lenses#67 absorbing-Markov chain uses (ℕ counting transition events, not
    fixed ticks). -/
inductive Support
  | discrete       -- ℕ, fixed ticks
  | eventIndexed   -- ℕ, counting transition events
  | continuous     -- ℝ
  deriving DecidableEq, Repr

/-! ## Kind — the NAME of the transition-functor family (taxonomy axis C) -/

/-- The declared kind names a transition-functor family; the record carries the
    NAME, and the semantics layer (bert-lenses#112) interprets it as an
    endofunctor. Grounded in the kinds shipped or scoped today; extensible as the
    taxonomy grows. -/
inductive DynamicsKind
  | conservation      -- Id-functor + additive conserved invariant (bert-compose)
  | markov            -- Dist(X), discrete-time (bert-lenses#67, absorbing)
  | deterministic     -- X^Σ, a deterministic automaton
  | nondeterministic  -- 𝒫(X), the powerset kind (the life-cycle ΔS ∈ F(S))
  deriving DecidableEq, Repr

/-! ## Invariant — a declared conserved quantity (taxonomy axis D) -/

/-- A conserved quantity is DECLARED, never assumed by the engine (axis D). At
    this vocabulary layer an invariant is named; its dimensional content is the
    kernel's units work (bert-lenses#94), not the record's. Conservation is one
    OPTIONAL declaration among several — `invariants = []` is the honest default
    for a kind that conserves nothing (e.g. a Markov chain). -/
structure Invariant where
  name : String
  deriving DecidableEq, Repr

/-! ## The record -/

/-- The declared Dynamics record: the structured refinement of Mobus's `τ`.
    Parametric in `Carrier` (the state space) and `Param` (the parameter payload
    of the kind's transfer-function family). -/
structure Dynamics (Carrier : Type*) (Param : Type*) where
  /-- The index shape (support) the dynamics is read against. -/
  support : Support
  /-- The transition-functor family, by name. -/
  kind : DynamicsKind
  /-- The declared conserved quantities (possibly none). -/
  invariants : List Invariant
  /-- The kind's transfer-function-family parameters. -/
  parameters : Param

namespace Dynamics

/-- A conservation record: discrete support, one declared conserved quantity —
    the compose engine's shape. Carrier-abstract, because conservation is a
    property of the declared invariant, not of the state-space type (keeping the
    file choice-free — an ℝ carrier would inherit `ℝ`'s `Classical.choice`). -/
def conservationExample (C : Type) : Dynamics C Unit where
  support := .discrete
  kind := .conservation
  invariants := [⟨"mass"⟩]
  parameters := ()

/-- The bill absorbing-Markov record (bert-lenses#67 ruling, 2026-07-23):
    event-indexed support, the Markov kind, NO conserved invariant, parameters =
    the transition weights over an abstract state carrier `C`. -/
def billMarkovExample (C : Type) (weights : List (C × C × Nat)) :
    Dynamics C (List (C × C × Nat)) where
  support := .eventIndexed
  kind := .markov
  invariants := []
  parameters := weights

/-- The two shipped/scoped kinds differ exactly where the theory says they must:
    conservation carries a conserved invariant, the Markov chain carries none. -/
example : (conservationExample Unit).invariants ≠ [] ∧
    (billMarkovExample Unit []).invariants = [] :=
  ⟨by decide, rfl⟩

end Dynamics

/-- Conservativity, machine-checked: a MobusSystem can carry the Dynamics record
    as its `τ`. Because `τ` participates in no coherence constraint (Tuple.lean),
    this refinement of the transform slot changes no structural field. -/
example (C P : Type) : Type _ :=
  MobusSystem (Fin 2) Unit Unit Unit (Dynamics C P) Unit Unit

end Systems
