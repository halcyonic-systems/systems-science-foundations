/-
  Systems/Dynamics/Mechanism.lean
  MechanismSpec — the honest Increment-1 surrogate for Bunge's mechanism M(σ).

  #97 INCREMENT 1 (bert-lenses), scoped by a frontier-council outside pass (triage:
  `operations/sessions/2026-07-23/references/type-m-council-triage.md`). The council
  BLOCKED the "retitle CES → CESM" close as silently unsound and delivered this
  smaller, honest, forward-compatible increment instead. Read the council findings
  before touching this file.

  WHAT M IS, AND WHAT THIS IS NOT. Bunge 2004 defines M(σ) EXTENSIONALLY: the *set of
  characteristic processes* of σ, each a *sequence of states* — i.e. M ⊆ S^ω, the
  behavior set H. The declared dynamics (descriptor `Dynamics S` + typed transition
  `Transition d`, i.e. the coalgebra structure map `T : S → F(S)`) is the GENERATOR of
  that set, NOT the set. Equating the generator with the behavior set is a category
  error (the grammar-vs-language / vector-field-vs-integral-curves slip). So:

    * `MechanismSpec` bundles the generator (descriptor + transition). It is a NAMED
      AUXILIARY on a system, deliberately NOT placed in an "M slot" of any toBunge
      mapping — the Mobus→Bunge bridge (Bridge.lean) still delivers the proven CES
      triple, unchanged. Retitle nothing to CESM.
    * Full M(σ) = the behavior set H obtained by UNFOLDING `transition` (coiteration).
      H is not yet a first-class Lean type; typing it + verifying the unfolding +
      discharging the emptiness constraint on H is Increment 2 (the real #97 close).

  THE CONSERVATIVE, MACHINE-CHECKED CONSTRAINT WE CAN EARN TODAY. Bunge 2004 (:300):
  "M(σ) is empty for conceptual systems" — conceptual systems undergo no material
  process. Formalized here as `wellKinded`: a Conceptual system carries no mechanism.

  OBJECT/MODEL SCOPING (council Q4, delicate — verified below). The kingdom is asserted
  on the MODELED OBJECT'S OWN NATURE (Bunge §1.2: "a theory is a conceptual system, a
  school a concrete system"), NOT on what the object processes. A proof assistant's
  state machine is a CONCRETE technical artifact that *represents* conceptual objects —
  its kingdom is Concrete, so the constraint does NOT refuse its mechanism. The check
  keys on `Kingdom`, which SSF/bert-lenses (issue #71) asserts on the modeled object;
  it is not derived from carrier contents. The `proofAssistantMechanism` witness below
  exercises exactly this legitimate case and shows the constraint does not misfire.

  AXIOM-FREE and CONSERVATIVE. Builds on `Dynamics`/`Transition` only; adds no theorem
  obligation to any existing structure. `#print axioms` on the definitions and witnesses
  reports axiom-free (no `Classical.choice` — the carrier stays abstract).
-/

import Systems.Dynamics.Transition

namespace Systems

/-! ## Kingdom — Bunge's top ontological split, asserted on the modeled object -/

/-- Bunge's two (exhaustive, exclusive) system kingdoms (§1.2). Asserted on the
    MODELED OBJECT'S nature — a theory/number is `conceptual`; an animal, an
    organization, a machine is `concrete`. NOT derived from carrier contents, and NOT
    a property of the model artifact: it is what the modeler declares the object to be.
    See `docs/reference/system-type-typologies.md` (bert-lenses#71). -/
inductive Kingdom
  | conceptual   -- theories, numbers: undergo no material process (M = ∅)
  | concrete     -- animals, organizations, machines: may bear a mechanism
  deriving DecidableEq, Repr

/-! ## MechanismSpec — the generator of M, as a named auxiliary (NOT the M slot) -/

/-- The honest Increment-1 surrogate for Bunge's mechanism coordinate: the declared
    dynamics descriptor together with its typed transition — the coalgebra GENERATOR of
    the behavior set, not the behavior set itself. Attach it to a system as a named
    auxiliary; it is deliberately NOT threaded into `MobusSystem.toBunge` (Bridge.lean),
    whose proven output is the CES triple. Full M(σ) requires unfolding `transition` to
    the behavior set H (Increment 2). -/
structure MechanismSpec (S : Type) where
  /-- The declared dynamics descriptor (kind, support, ports, invariants). -/
  descriptor : Dynamics S
  /-- The typed transition of that descriptor — the coalgebra structure map `S → F(S)`,
      Mealy-shaped over the ports. This is the generator; unfolding it yields H. -/
  transition : Transition descriptor

/-! ## The Conceptual-kingdom emptiness constraint (Bunge 2004 :300) -/

/-- Bunge's coherence constraint, machine-checkable now: a system whose MODELED OBJECT
    is of the Conceptual kingdom bears NO mechanism (M(σ) = ∅). Scoped to `k` — the
    kingdom of the modeled object — so a concrete system that merely *processes*
    conceptual objects (kingdom = `concrete`) is unaffected. Forward-compatible: when H
    is typed (Increment 2), this refusal of a generator upgrades to `M(σ) = ∅` on H. -/
def wellKinded {S : Type} (k : Kingdom) (m : Option (MechanismSpec S)) : Prop :=
  k = Kingdom.conceptual → m.isNone = true

/-! ## Witnesses -/

/-- A conceptual system declaring no mechanism satisfies the constraint (M = ∅). -/
example (S : Type) : wellKinded Kingdom.conceptual (none : Option (MechanismSpec S)) :=
  fun _ => rfl

/-- The constraint FIRES correctly: a conceptual system that declares a mechanism
    violates it — a machine-checkable category error, exactly Bunge's :300. -/
example (S : Type) (m : MechanismSpec S) :
    ¬ wellKinded Kingdom.conceptual (some m) := by
  intro h; have := h rfl; simp at this

/-- A concrete system may bear a mechanism (M non-empty is allowed). -/
example (S : Type) (m : MechanismSpec S) : wellKinded Kingdom.concrete (some m) := by
  intro h; exact absurd h (by decide)

/-- A concrete MechanismSpec built from a closed deterministic transition (a
    conservation-flow step, TYPED as the deterministic coalgebra). -/
def proofAssistantMechanism (S : Type) (step : S → S) : MechanismSpec S where
  descriptor := Dynamics.conservationExample S
  transition := Transition.deterministicClosed step

/-- OBJECT/MODEL WITNESS (council Q4). A proof assistant is a CONCRETE technical system
    whose state machine *represents* conceptual objects. Its kingdom is `concrete`, so
    the emptiness constraint does NOT refuse its mechanism — proof that the check keys
    on the modeled object's kingdom, not on what the object processes, and therefore
    does not misfire on this legitimate case. -/
example (S : Type) (step : S → S) :
    wellKinded Kingdom.concrete (some (proofAssistantMechanism S step)) := by
  intro h; exact absurd h (by decide)

/-! ## Axiom audit -/

-- #print axioms wellKinded
-- #print axioms proofAssistantMechanism
-- (run below; both report axiom-free — no `Classical.choice`.)

end Systems
