/-
  Systems/Core/InternalModel.lean
  Principle 9: Internal Models — a system contains a model that tracks another system

  Mobus, Systems Science: "Systems contain models of other systems (e.g., simple
  built-in protocols for interaction with other systems and up to complex
  anticipatory models)."

  The tractable core of Internal Models (per the roadmap) is the SIMULATION
  RELATION: a subsystem R holds a representation `model : R → S` of system S, and
  R's internal dynamics commute with S's dynamics through that map:

      R --internalDyn--> R
      |                   |
    model               model
      ↓                   ↓
      S --systemDyn ----> S        (one-step square commutes)

  This is precisely `Function.Semiconj model internalDyn systemDyn` — a dynamics
  homomorphism. The scientific claim worth proving: a model that is correct for
  ONE step is correct for ALL steps. That lifting is what makes a model
  *anticipatory* — it predicts the system arbitrarily far ahead, not just next.

  Connection to the ontology:
  - The map `model : R → S` is the same homomorphism the Conant-Ashby skeleton
    (Lens.lean, Principle 8) requires of a good regulator. An internal model
    IS the structure governance needs — #9 and #8 share the walking arrow.
  - The walking arrow K ≅ **2**: a system is a morphism; an internal model is a
    morphism; the regulator's model is a morphism. Same irreducible content.

  Deferred (research-level, not axiomatization gaps):
  - Stochastic / approximate models (requires a metric or probability on S)
  - Self-models (#10): the case S = R, needing fixed-point machinery (Lawvere)
-/

import Systems.Core.Governance

namespace Systems

/-! ## Internal Model

  A subsystem R that holds a model of system S, with internal dynamics that
  simulate S's dynamics through the model map. -/

/-- An internal model: subsystem state space `R` carries a representation
    `model : R → S` of system `S`, and R's internal dynamics `internalDyn`
    simulate S's actual dynamics `systemDyn` one step at a time.

    The `simulates` field is the one-step commuting square — a dynamics
    homomorphism (`Function.Semiconj model internalDyn systemDyn`). It is the
    minimal, set-theoretic core of "R contains a model of S": evolving the
    model then reading it off equals reading it off then evolving the system. -/
structure InternalModel (R S : Type*) where
  /-- R's internal representation of S (the modelling homomorphism). -/
  model : R → S
  /-- How the model evolves inside R. -/
  internalDyn : R → R
  /-- The actual dynamics of the modelled system S. -/
  systemDyn : S → S
  /-- One-step simulation: the model commutes with the dynamics. -/
  simulates : ∀ r, model (internalDyn r) = systemDyn (model r)

/-! ## The model tracks the system at every horizon

  The central theorem: one-step correctness lifts to n-step correctness. -/

/- PROOF TARGET: an internal model correct for one step is correct for all steps.

   MATHEMATICAL INTENT:
   model (internalDyn^[n] r) = systemDyn^[n] (model r) for every n.
   The model's n-step internal evolution, read off, equals the system's actual
   n-step evolution from the modelled state. This is what "anticipatory model"
   means precisely: a correct one-step model is a correct predictor at any depth.

   AVAILABLE TOOLS:
   - `InternalModel.simulates` (the one-step commuting square)
   - `Function.iterate_succ_apply : f^[n+1] x = f^[n] (f x)`

   STRATEGY HINT:
   Induction on n, generalizing r. Unfold both iterates by one step, apply the
   inductive hypothesis at `internalDyn r`, then the one-step simulation. -/
theorem InternalModel.tracks {R S : Type*} (im : InternalModel R S) (n : ℕ) (r : R) :
    im.model (im.internalDyn^[n] r) = im.systemDyn^[n] (im.model r) := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        ih (im.internalDyn r), im.simulates]

/-- The model's n-step prediction from an internal state. -/
def InternalModel.predict {R S : Type*} (im : InternalModel R S) (n : ℕ) (r : R) : S :=
  im.model (im.internalDyn^[n] r)

/-- Anticipation: the model's n-step prediction equals the system's actual
    n-step evolution from the modelled state. The internal model is a correct
    predictor at every horizon — the formal content of "anticipatory model." -/
theorem InternalModel.predict_correct {R S : Type*} (im : InternalModel R S)
    (n : ℕ) (r : R) :
    im.predict n r = im.systemDyn^[n] (im.model r) :=
  im.tracks n r

/-- An internal equilibrium maps to a system equilibrium: if the model is at
    rest internally, the state it represents is at rest in the system. The
    simulation relation carries fixed points forward through the model. -/
theorem InternalModel.equilibrium_image {R S : Type*} (im : InternalModel R S)
    {r : R} (h : IsEquilibrium im.internalDyn r) :
    IsEquilibrium im.systemDyn (im.model r) := by
  unfold IsEquilibrium at *
  rw [← im.simulates, h]

/-! ## Bridge to Conant-Ashby (Governance #8) and the walking arrow

  An internal model is exactly the homomorphism a good regulator must contain. -/

/-- Every internal model yields a Conant-Ashby skeleton under any observation
    of S: the modelling map `model : R → S` is the regulator's homomorphic
    model, and the regulator's view factors through it (`regView = observe ∘ model`).

    This makes the #9 → #8 dependency concrete: having an internal model of a
    system supplies precisely the structure Conant-Ashby (1970) requires of a
    good regulator. Both are the walking arrow K ≅ **2** — "modelling a system"
    and "governing a system" share one irreducible morphism. -/
def InternalModel.toConantAshby {R S : Type*} (im : InternalModel R S)
    {O : Type*} (observe : S → O) : ConantAshbySkeleton R S O where
  model := im.model
  observe := observe
  regView := observe ∘ im.model
  model_compatible := rfl

/-! ## Anticipatory models (Rosen): the model runs ahead of the system

  Rosen's anticipatory system is a system whose internal model runs FASTER than
  the system it models — per internal tick, the model advances `lead` system
  steps. `InternalModel` is exactly the `lead = 1` case. -/

/-- An anticipatory model: like `InternalModel`, but one internal tick of R
    advances the modelled system by `lead` steps. The `simulates` square now
    commutes with `systemDyn^[lead]` — the Rosen fast-model shape. -/
structure AnticipatoryModel (R S : Type*) where
  /-- R's internal representation of S. -/
  model : R → S
  /-- How the model evolves inside R. -/
  internalDyn : R → R
  /-- The actual dynamics of the modelled system S. -/
  systemDyn : S → S
  /-- System-steps gained per internal tick. -/
  lead : ℕ
  /-- One internal tick simulates `lead` system steps. -/
  simulates : ∀ r, model (internalDyn r) = systemDyn^[lead] (model r)

/- PROOF TARGET: an anticipatory model correct for one tick is correct at
   every horizon, with the lead compounding.

   MATHEMATICAL INTENT:
   model (internalDyn^[n] r) = systemDyn^[n * lead] (model r) for every n.
   After n internal ticks the model has raced n * lead system-steps ahead —
   the growing lead that makes the model genuinely anticipatory (Rosen).
   At lead = 1 this is exactly InternalModel.tracks.

   AVAILABLE TOOLS:
   - `AnticipatoryModel.simulates` (the one-tick, lead-step square)
   - `Function.iterate_succ_apply : f^[n+1] x = f^[n] (f x)`
   - `Function.iterate_add_apply : f^[m+n] x = f^[m] (f^[n] x)`
   - `Nat.succ_mul : (n+1) * m = n * m + m`

   STRATEGY HINT:
   Induction on n, generalizing r — same skeleton as InternalModel.tracks,
   then collapse the composed iterates with iterate_add_apply and succ_mul. -/
theorem AnticipatoryModel.tracks {R S : Type*} (am : AnticipatoryModel R S)
    (n : ℕ) (r : R) :
    am.model (am.internalDyn^[n] r) = am.systemDyn^[n * am.lead] (am.model r) := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih (am.internalDyn r), am.simulates,
        ← Function.iterate_add_apply, Nat.succ_mul]

/-! ## Round-trip: `InternalModel` is the `lead = 1` case -/

/-- Every internal model is an anticipatory model with unit lead. -/
def InternalModel.toAnticipatory {R S : Type*} (im : InternalModel R S) :
    AnticipatoryModel R S where
  model := im.model
  internalDyn := im.internalDyn
  systemDyn := im.systemDyn
  lead := 1
  simulates := by simpa using im.simulates

/-- At unit lead, anticipatory tracking specializes to `InternalModel.tracks`:
    the round-trip confirming `AnticipatoryModel` generalizes `InternalModel`
    rather than sitting beside it. -/
theorem InternalModel.toAnticipatory_tracks {R S : Type*} (im : InternalModel R S)
    (n : ℕ) (r : R) :
    im.toAnticipatory.model (im.toAnticipatory.internalDyn^[n] r)
      = im.systemDyn^[n] (im.model r) := by
  simpa [InternalModel.toAnticipatory] using im.toAnticipatory.tracks n r

end Systems
