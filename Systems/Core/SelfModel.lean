/-
  Systems/Core/SelfModel.lean
  Principle 10: Self-Models — a system that contains a model of itself

  Mobus, Systems Science: "Sufficiently complex, adaptive systems can contain
  self-models."

  A self-model is the DIAGONAL CASE of an Internal Model (#9): the modelled
  system is the containing system itself. Where `InternalModel R S` has a
  subsystem R holding a model of a *different* system S, a self-model has one
  state space S whose internal representation `selfModel : S → S` tracks S's
  OWN dynamics:

      S --dyn-------> S
      |               |
   selfModel      selfModel
      ↓               ↓
      S --dyn-------> S        (the self-simulation square commutes)

  This is `InternalModel S S` with `internalDyn = systemDyn = dyn` — the system
  models the same dynamics it runs. We make that reuse explicit
  (`toInternalModel`) so every #9 result transfers for free:

  - tracks → SELF-PREDICTION: a correct one-step self-model predicts the
    system's own future at every horizon (anticipatory self-model).
  - equilibrium_image → a self-modelled fixed point stays a fixed point.

  Scientific honesty (the self-reference content, scoped not overclaimed):
  - EXISTENCE is trivial. `selfModel = id` always commutes with `dyn`, so every
    system has a (degenerate) self-model (`SelfModel.trivial`). The substance is
    never "does a self-model exist" but "is it FAITHFUL / non-trivial."
  - The genuinely self-referential fact we CAN prove: a state the model
    represents as itself (`selfModel s = s`, a self-consistent self-image) stays
    self-consistent under the dynamics (`accurate_invariant`). The accurate set
    is dynamics-invariant — a fixed-point flavour without heavy machinery.

  Deferred (research-level — see roadmap §"Principle 10"):
  - EXISTENCE/OBSTRUCTION for a faithful self-model via Lawvere's fixed-point
    theorem. Mathlib has only the powerset diagonal (`Function.cantor_surjective`),
    not a general Lawvere theorem, so the categorical "a proper part cannot
    perfectly model the whole" limitation must be built from scratch. The
    diagonal argument is the next, separate session.
-/

import Systems.Core.InternalModel

namespace Systems

variable {S : Type*}

/-! ## Self-Model

  A system whose state space carries a model of its own dynamics. -/

/-- A self-model: a system with dynamics `dyn : S → S` together with an internal
    self-representation `selfModel : S → S` that simulates the system's OWN
    dynamics one step at a time.

    `self_simulates` is the self-simulation square — the diagonal instance of
    `InternalModel.simulates` with the modelled system equal to the container.
    It says: evolving the system then re-reading the self-model equals reading
    the self-model then evolving — the self-model is a dynamics endomorphism
    (`Function.Semiconj selfModel dyn dyn`). -/
structure SelfModel (S : Type*) where
  /-- The system's own dynamics. -/
  dyn : S → S
  /-- The system's internal model of itself. -/
  selfModel : S → S
  /-- One-step self-simulation: the self-model commutes with the dynamics. -/
  self_simulates : ∀ s, selfModel (dyn s) = dyn (selfModel s)

/-- A self-model IS the diagonal internal model: an `InternalModel S S` whose
    internal and system dynamics are the single shared `dyn`. This is the formal
    content of "#10 is the S = R case of #9" — every Internal-Model result
    transfers through this map. -/
def SelfModel.toInternalModel (sm : SelfModel S) : InternalModel S S where
  model := sm.selfModel
  internalDyn := sm.dyn
  systemDyn := sm.dyn
  simulates := sm.self_simulates

/-! ## Self-prediction at every horizon

  The anticipatory self-model: one-step self-correctness lifts to all steps,
  inherited from `InternalModel.tracks`. -/

/-- A correct one-step self-model predicts the system's OWN future at every
    horizon: reading the self-model after n internal steps equals the system's
    actual n-step evolution of the represented state. This is anticipation
    turned inward — the system foresees itself — and it is structural, free
    from #9's induction. -/
theorem SelfModel.tracks (sm : SelfModel S) (n : ℕ) (s : S) :
    sm.selfModel (sm.dyn^[n] s) = sm.dyn^[n] (sm.selfModel s) :=
  sm.toInternalModel.tracks n s

/-- The self-model's n-step self-prediction from a state. -/
def SelfModel.predict (sm : SelfModel S) (n : ℕ) (s : S) : S :=
  sm.selfModel (sm.dyn^[n] s)

/-- Anticipatory self-model: the n-step self-prediction equals the system's
    actual n-step evolution of the represented state, at every horizon. -/
theorem SelfModel.predict_correct (sm : SelfModel S) (n : ℕ) (s : S) :
    sm.predict n s = sm.dyn^[n] (sm.selfModel s) :=
  sm.tracks n s

/-- A self-modelled equilibrium stays an equilibrium: if a state is at rest
    under the dynamics, so is the state its self-model represents. The
    self-simulation square carries the system's fixed points through its own
    model. -/
theorem SelfModel.equilibrium_image (sm : SelfModel S) {s : S}
    (h : IsEquilibrium sm.dyn s) :
    IsEquilibrium sm.dyn (sm.selfModel s) :=
  sm.toInternalModel.equilibrium_image h

/-! ## Existence is trivial; faithfulness is the content

  Every system self-models degenerately via the identity. The scientific
  weight is in non-trivial self-models, so we anchor that honesty here. -/

/-- The trivial self-model: the identity is always a self-model, since `id`
    commutes with any dynamics. Hence EVERY system has a self-model — existence
    is free, and the real question is faithfulness/non-triviality, not
    existence. -/
def SelfModel.trivial (dyn : S → S) : SelfModel S where
  dyn := dyn
  selfModel := id
  self_simulates := fun _ => rfl

/-! ## Self-consistency: the fixed points of the self-model are invariant

  The one genuinely self-referential result the set-theoretic core supports:
  states the model represents as themselves form a dynamics-invariant set. -/

/-- A state is accurately self-modelled when the self-model represents it as
    itself: `selfModel s = s`. This is a self-consistent self-image — the model
    and the modelled coincide on `s` (a fixed point of the model map). -/
def SelfModel.accurate (sm : SelfModel S) (s : S) : Prop := sm.selfModel s = s

/-- Self-consistency is preserved by the dynamics: if the self-model represents
    `s` as itself, it represents `dyn s` as itself too. The accurate set is
    invariant under evolution — the self-image, once correct, stays correct as
    the system runs. This is the self-reference loop closing into itself
    (`selfModel (dyn s) = dyn (selfModel s) = dyn s`) without Lawvere machinery. -/
theorem SelfModel.accurate_invariant (sm : SelfModel S) {s : S}
    (h : sm.accurate s) : sm.accurate (sm.dyn s) := by
  unfold SelfModel.accurate at *
  rw [sm.self_simulates, h]

end Systems
