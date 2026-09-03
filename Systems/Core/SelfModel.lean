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

/-- Mobus (2022, 2-principles-of-systems-science.md:238): "Sufficiently complex, adaptive systems can contain
    self-models."
    Mobus (2022, 2-principles-of-systems-science.md:368): "Creatures capable of having mentally mediated roles and
    identities include models of themselves, and these likewise may involve greater or lesser
    accuracy."
    Encoding: the system→`dyn : S → S`; "models of themselves"→`selfModel : S → S` on the same
    state space, tracking `dyn` via `self_simulates`; "greater or lesser accuracy"→`accurate`
    (pointwise: `selfModel s = s`).
    Not encoded: "sufficiently complex, adaptive" (no complexity or adaptivity precondition —
    every system has `SelfModel.trivial`); "contain" as part–whole (model and modelled share
    one state space); graded accuracy (exact-or-not, no metric); "mentally mediated roles and
    identities".

    A self-model: a system with dynamics `dyn : S → S` together with an internal
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

/-! ## Fast self-models (Rosen): a system whose self-model outruns it

  The diagonal of `AnticipatoryModel`: one state space whose self-representation
  advances `lead` steps of its OWN dynamics per system tick. The diagonal owns
  content the lockstep `SelfModel` does not: accuracy and speed fight. A
  lockstep self-image, once correct, stays correct (`accurate_invariant`); a
  genuinely fast one (`lead ≥ 2`) can only stay correct on a nearly-static
  orbit — perfect self-anticipation collapses time. -/

/-- Mobus (2022, 2-principles-of-systems-science.md:238): "Sufficiently complex, adaptive systems can contain
    self-models."
    Source: Rosen, Anticipatory Systems (1985) — verbatim not in vault.
    Encoding: "self-models"→`selfModel : S → S` against the system's own `dyn`; anticipation→
    `lead` steps of `dyn` per tick in `self_simulates`; accuracy→`accurate`.
    Not encoded: "sufficiently complex, adaptive" (no precondition); "contain" as part–whole;
    graded accuracy.

    A fast self-model: the system's self-representation gains `lead` steps of
    the system's own dynamics per tick — `AnticipatoryModel S S` with one
    shared `dyn` (the diagonal), as `SelfModel` is the diagonal of
    `InternalModel`. -/
structure FastSelfModel (S : Type*) where
  /-- The system's own dynamics. -/
  dyn : S → S
  /-- The system's internal model of itself. -/
  selfModel : S → S
  /-- System-steps of `dyn` gained per tick. -/
  lead : ℕ
  /-- One tick of the self-model simulates `lead` steps of the system. -/
  self_simulates : ∀ s, selfModel (dyn s) = dyn^[lead] (selfModel s)

/-- A fast self-model IS the diagonal anticipatory model: an
    `AnticipatoryModel S S` whose internal and system dynamics are the single
    shared `dyn`. Every `AnticipatoryModel` result transfers through this map. -/
def FastSelfModel.toAnticipatory (fsm : FastSelfModel S) : AnticipatoryModel S S where
  model := fsm.selfModel
  internalDyn := fsm.dyn
  systemDyn := fsm.dyn
  lead := fsm.lead
  simulates := fsm.self_simulates

/-- Fast self-prediction at every horizon: after n system steps the self-model
    has raced `n * lead` steps ahead of the represented state — the compounding
    lead of `AnticipatoryModel.tracks`, turned inward. -/
theorem FastSelfModel.tracks (fsm : FastSelfModel S) (n : ℕ) (s : S) :
    fsm.selfModel (fsm.dyn^[n] s) = fsm.dyn^[n * fsm.lead] (fsm.selfModel s) :=
  fsm.toAnticipatory.tracks n s

/-- A state is accurately self-modelled when the fast self-model represents it
    as itself: `selfModel s = s` — same self-consistency as
    `SelfModel.accurate`. -/
def FastSelfModel.accurate (fsm : FastSelfModel S) (s : S) : Prop :=
  fsm.selfModel s = s

/- PROOF TARGET: accuracy at both ends of an orbit segment collapses the fast
   clock onto the slow one.

   MATHEMATICAL INTENT:
   If the self-model is accurate at s and at dyn^[n] s, then
   dyn^[n * lead] s = dyn^[n] s: running the system n*lead steps lands exactly
   where n steps land. A faithful fast self-model cannot outrun its system —
   it forces the fast and slow clocks to agree on the orbit.

   AVAILABLE TOOLS:
   - `FastSelfModel.tracks` (compounding lead)
   - both accuracy hypotheses as rewrite equations

   STRATEGY HINT:
   Rewrite the slow side by accuracy at dyn^[n] s, apply tracks, then accuracy
   at s. -/
theorem FastSelfModel.accurate_collapse (fsm : FastSelfModel S) {s : S} {n : ℕ}
    (h1 : fsm.accurate s) (h2 : fsm.accurate (fsm.dyn^[n] s)) :
    fsm.dyn^[n * fsm.lead] s = fsm.dyn^[n] s := by
  unfold FastSelfModel.accurate at h1 h2
  rw [← h2, fsm.tracks, h1]

/- PROOF TARGET: perfect self-anticipation collapses time — an accurate fast
   self-model forces its orbit point into periodicity.

   MATHEMATICAL INTENT:
   Under the same accuracy hypotheses, dyn^[n*(lead-1)] (dyn^[n] s) = dyn^[n] s:
   the reached orbit point is periodic with period dividing n*(lead-1). For a
   genuinely fast model (lead ≥ 2, n ≥ 1) that is nontrivial periodicity — a
   faithful self-oracle can only exist over a nearly-static future. Contrast
   lead = 1: the exponent is 0 and the statement is trivially true, which is
   exactly why lockstep accuracy is invariant (`SelfModel.accurate_invariant`)
   with no constraint on the dynamics.

   AVAILABLE TOOLS:
   - `FastSelfModel.accurate_collapse`
   - `Function.iterate_add_apply : f^[m+n] x = f^[m] (f^[n] x)`
   - `Nat.mul_succ`, `Nat.succ_pred_eq_of_pos` for the truncated subtraction

   STRATEGY HINT:
   Fuse the iterates with iterate_add_apply, split on lead = 0 vs lead ≥ 1 to
   resolve n*(lead-1) + n = n*lead through the truncated subtraction, then
   close with accurate_collapse. -/
theorem FastSelfModel.accurate_forces_periodic (fsm : FastSelfModel S) {s : S}
    {n : ℕ} (h1 : fsm.accurate s) (h2 : fsm.accurate (fsm.dyn^[n] s)) :
    fsm.dyn^[n * (fsm.lead - 1)] (fsm.dyn^[n] s) = fsm.dyn^[n] s := by
  rw [← Function.iterate_add_apply]
  rcases Nat.eq_zero_or_pos fsm.lead with h0 | hpos
  · simp [h0]
  · have harith : n * (fsm.lead - 1) + n = n * fsm.lead := by
      -- why: succ_pred lemmas speak in Nat.pred while the goal has `- 1`;
      -- reduce to the linear index equation and close it arithmetically
      rw [← Nat.mul_succ]
      congr 1
      omega
    rw [harith]
    exact fsm.accurate_collapse h1 h2

/-! ## Accuracy is NOT invariant for fast self-models

  The seam with the lockstep case, by concrete witness. `SelfModel` proves
  `accurate_invariant`: a correct self-image stays correct. For `lead ≥ 2`
  that fails — accuracy at s forces `selfModel (dyn s) = dyn^[lead] s`, which
  is ahead of `dyn s` unless the orbit is degenerate. -/

/-- The doubling witness: `ℕ` under successor, self-modelled by doubling at
    `lead = 2`. One tick of doubling gains two successor steps
    (`2·(s+1) = (2·s) + 2`), so this is a genuinely fast self-model. -/
def FastSelfModel.doubling : FastSelfModel ℕ where
  dyn := Nat.succ
  selfModel := (2 * ·)
  lead := 2
  self_simulates := fun s => by
    simp [Function.iterate_succ_apply', Nat.mul_succ]

/-- Accuracy is not invariant once the self-model genuinely outruns the system:
    the doubling witness is accurate at 0 (`2·0 = 0`) but NOT at `dyn 0 = 1`
    (`2·1 ≠ 1`). Contrast `SelfModel.accurate_invariant`, where lockstep
    accuracy propagates unconditionally — the invariance of self-consistency is
    a lockstep privilege, not a general fact about self-models. -/
theorem FastSelfModel.doubling_accurate_not_invariant :
    FastSelfModel.doubling.accurate 0 ∧
      ¬ FastSelfModel.doubling.accurate (FastSelfModel.doubling.dyn 0) := by
  constructor
  · rfl
  · intro h
    simp [FastSelfModel.accurate, FastSelfModel.doubling] at h

end Systems
