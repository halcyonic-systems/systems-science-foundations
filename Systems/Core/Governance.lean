/-
  Systems/Core/Governance.lean
  Principle 8: Governance — goal-directed regulation via feedback

  Mobus, Systems Science: Theory, Analysis, Modeling, and Design, Ch. 12:
  "The key to the success of a CAES in continuing to be viable within its
   embedding supra-system is that it is capable of stable management of
   its economy."

  INDEPENDENCE ARGUMENT: Governance adds three primitives not present in
  Principles #1-#4:
  1. A reference state (set point) — what the system aims to maintain
  2. An error function — comparison of actual vs desired
  3. Asymmetric feed-downward — higher levels modify lower levels' parameters

  CoupledDynamicSystem captures mutual influence but has no notion of
  "where we want to be." The set point is genuinely new structure. The
  feedback cycle in ShapeJoslyn (afferent: sense error, efferent: correct
  error) is the categorical signature of this new structure.

  Key definitions:
  - Homeostat: the fundamental governance unit (Ashby/Wiener)
  - GovernanceSubsystem: a distinguished regulator with reference state
  - HCGS: hierarchical governance mapped to TimescaleDecomposition levels
-/

import Systems.Core.Lens

namespace Systems

/-! ## Homeostat (Ashby 1958 / Wiener 1961)

  The fundamental unit of cybernetic governance: a process controlled
  by negative feedback against a reference state.

  Mobus Ch. 12, §12.3.2: "The basic theory of cybernetics is the use
  of feedback information to cause a system to modify its activities
  in order to maintain an output function in a viable or nominal value
  range in the face of disturbances."

  The homeostat is the building block of all governance. Every work
  process in every CAS/CAES is managed by some form of homeostat.
  The HCGS is a hierarchy of homeostats operating at different time
  scales. -/

/-- Mobus (2022, 2-principles-of-systems-science.md:236): "Systems have governance subsystems to achieve stability."
    Mobus (2022, 12-governance-model.md:307): "The basic theory of cybernetics is the use of
    feedback information to cause a system to modify its activities in order to maintain an
    output function in a viable or nominal value range in the face of disturbances that might
    otherwise cause the output to deviate from a desired value. The system is goal-maintaining
    in this sense."
    Mobus (2022, 12-governance-model.md:309): "If a disturbance to the process causes the value
    to vary from an ideal, as represented by the "set point" constant, either higher or lower,
    an error signal is generated and fed back to the computational engine that uses the
    control model. This information is used to generate a control signal that activates an
    actuator (e.g., a motor) that changes the internal operations of the work process in
    opposition to the error."
    Source: Ashby, Design for a Brain (homeostat) — verbatim not in vault.
    Encoding: "set point constant" / "desired value"→`setPoint`; output value→`sensor`;
    "error signal"→`error`; "control signal ... changes the internal operations"→`correct`;
    "feedback"→`feedbackLaw` (sense → compare → correct); "goal-maintaining" / "stability"→
    `atTarget`, `target_is_equilibrium`.
    Not encoded: "in opposition to the error" (`correct` carries no sign or direction
    constraint — negative feedback is not enforced); disturbances (no input); "value range"
    (a single point, not a band); stability as attraction (only a fixed point is shown, not
    convergence to it); "subsystem" (no `ConcreteSystem` here — `GovernanceSubsystem` adds it).

    A homeostat: the basic cybernetic control unit.

    Given a state space S with a measurable output O:
    - `setPoint`: the desired output value (reference state)
    - `sensor`: extracts the observable output from the state
    - `error`: computes the deviation from the set point
    - `correct`: generates a corrective state transition from the error

    The feedback loop: sense → compare → correct → repeat.
    This is what ShapeJoslyn's cycle encodes categorically. -/
structure Homeostat (S : Type*) (O : Type*) where
  setPoint : O
  sensor : S → O
  error : O → O → O
  correct : O → S → S

/-- The feedback law: given a state, sense the output, compute error
    against the set point, apply correction. This is the composed
    governance action — one tick of the feedback loop. -/
def Homeostat.feedbackLaw {S O : Type*} (h : Homeostat S O) : S → S :=
  fun s => h.correct (h.error (h.sensor s) h.setPoint) s

/-- A state is at the governance target when the sensor reads the set point.
    This is the equilibrium condition specific to governance: not just
    any fixed point, but the INTENDED fixed point. -/
def Homeostat.atTarget {S O : Type*} (h : Homeostat S O) (s : S) : Prop :=
  h.sensor s = h.setPoint

/-- A homeostat viewed as a lens: sensor is get, error-then-correct is put.

    The lens captures the bidirectional channel of governance:
    - Forward (get = sensor): observe the system state
    - Backward (put): compute error against setPoint, apply correction

    The setPoint and error function are baked into the put channel.
    This is the formal content of "a homeostat is a lens plus a reference
    value": the reference value parameterizes the backward channel.

    Three modern frameworks (Capucci et al. categorical cybernetics,
    Spivak-Niu polynomial functors, Myers CST) identify this structure.
    Our Homeostat is their concrete instance for Mobus's HCGS. -/
def Homeostat.toLens {S O : Type*} (h : Homeostat S O) : Lens S O O where
  get := h.sensor
  put := fun s o => h.correct (h.error o h.setPoint) s

/-- The feedback law decomposes as get-then-put: observe, then correct.

    feedbackLaw s = toLens.put s (toLens.get s)

    This decomposition reveals the bidirectional structure hidden in
    the monolithic feedbackLaw: sense (forward channel) then correct
    (backward channel). The lens makes the two directions explicit. -/
theorem Homeostat.feedbackLaw_eq_lens {S O : Type*}
    (h : Homeostat S O) (s : S) :
    h.feedbackLaw s = h.toLens.put s (h.toLens.get s) := by
  rfl

/-- Compose two homeostats through their lens structure.

    Given h₁ on state S with observable O, and h₂ on O with observable P,
    the composed lens observes P from S and corrects S through the chain.
    This is what TwoLevelGovernance does manually — lens composition
    does it structurally, for free. -/
def Homeostat.composeLens {S O P : Type*}
    (h₁ : Homeostat S O) (h₂ : Homeostat O P) : Lens S P P :=
  h₁.toLens.compose h₂.toLens

/-- If error at target is zero (error of identical values is neutral)
    and correction with zero error is identity, then the target IS
    an equilibrium of the feedback law.

    This connects governance equilibrium to dynamical equilibrium:
    the governance target is a fixed point of the feedback law. -/
theorem Homeostat.target_is_equilibrium {S O : Type*}
    (h : Homeostat S O) (s : S)
    (h_at : h.atTarget s)
    (h_error_zero : ∀ o, h.error o o = h.error h.setPoint h.setPoint)
    (h_correct_neutral : ∀ s', h.correct (h.error h.setPoint h.setPoint) s' = s') :
    IsEquilibrium h.feedbackLaw s := by
  unfold IsEquilibrium Homeostat.feedbackLaw Homeostat.atTarget at *
  rw [h_at, h_correct_neutral]

/-! ## Governance Subsystem

  A governance subsystem is a distinguished part of a system whose
  dynamics regulate another part. It extends CoupledDynamicSystem
  with a reference state and error function — the new structure
  that makes governance independent of Dynamics (#4).

  Mobus Ch. 12, §12.2.1: "The governance subsystem is that which
  ensures the smooth and efficient working of the whole economy
  for the benefit of all of its components." -/

/-- A governance subsystem: a regulator coupled to a regulated process.

    The regulator (governor) observes the regulated process's state,
    compares it to a reference, and acts to reduce the error. This
    extends CoupledDynamicSystem with:
    - A reference state (set point) for the regulated process
    - A sensor extracting observable output from the regulated state
    - An error function comparing actual to desired

    The governor's law depends on the error signal, not directly on
    the regulated state. This is the asymmetry that governance adds:
    the governor acts through the error, not through raw coupling. -/
structure GovernanceSubsystem (α : Type*) [ActsOn α]
    (S_gov S_reg O : Type*) where
  system : ConcreteSystem α
  setPoint : O
  sensor : S_reg → O
  error : O → O → O
  govLaw : S_gov → O → S_gov
  regLaw : S_reg → S_gov → S_reg

/-- The combined law of a governance subsystem on the product state space.
    The governor sees the error signal (not raw regulated state).
    The regulated process sees the governor's output. -/
def GovernanceSubsystem.combinedLaw {α : Type*} [ActsOn α]
    {S_gov S_reg O : Type*}
    (gs : GovernanceSubsystem α S_gov S_reg O) :
    S_gov × S_reg → S_gov × S_reg :=
  fun (sg, sr) =>
    let err := gs.error (gs.sensor sr) gs.setPoint
    (gs.govLaw sg err, gs.regLaw sr sg)

/-- A governance equilibrium: the regulated process is at the target
    AND the governor is at rest. -/
def GovernanceEquilibrium {α : Type*} [ActsOn α]
    {S_gov S_reg O : Type*}
    (gs : GovernanceSubsystem α S_gov S_reg O)
    (sg : S_gov) (sr : S_reg) : Prop :=
  gs.sensor sr = gs.setPoint ∧
  gs.govLaw sg (gs.error gs.setPoint gs.setPoint) = sg ∧
  gs.regLaw sr sg = sr

/-- A governance equilibrium is a fixed point of the combined law,
    given that error at the set point is self-consistent. -/
theorem GovernanceSubsystem.equilibrium_is_fixed
    {α : Type*} [ActsOn α] {S_gov S_reg O : Type*}
    (gs : GovernanceSubsystem α S_gov S_reg O)
    {sg : S_gov} {sr : S_reg}
    (h_eq : GovernanceEquilibrium gs sg sr) :
    IsEquilibrium gs.combinedLaw (sg, sr) := by
  unfold IsEquilibrium GovernanceSubsystem.combinedLaw GovernanceEquilibrium at *
  obtain ⟨h_target, h_gov, h_reg⟩ := h_eq
  simp [h_target, h_gov, h_reg]

/-- A GovernanceSubsystem induces a CoupledDynamicSystem by forgetting
    the reference state and error function.

    This is the formal content of "governance extends dynamics":
    every governance subsystem IS a coupled system, but not every
    coupled system has governance structure. The set point and error
    function are the additional structure. -/
def GovernanceSubsystem.toCoupled {α : Type*} [ActsOn α]
    {S_gov S_reg O : Type*}
    (gs : GovernanceSubsystem α S_gov S_reg O) :
    CoupledDynamicSystem α S_gov S_reg where
  system := gs.system
  law₁ := fun sg sr => gs.govLaw sg (gs.error (gs.sensor sr) gs.setPoint)
  law₂ := fun sg sr => gs.regLaw sr sg

/-! ## Hierarchical Cybernetic Governance System (HCGS)

  The HCGS is a layered governance architecture where each level
  operates on a longer time scale than the one below:
  - Operations: real-time homeostatic control (fast)
  - Coordination: logistical + tactical management (medium)
  - Strategic: structural self-modification (slow)

  This maps directly to TimescaleDecomposition: the HCGS IS a
  timescale decomposition where each level has its own Homeostat
  with its own set point. Higher levels modify lower levels'
  set points — the feed-downward mechanism.

  Mobus Ch. 12, §12.3: "The model of an HCGS is derived from
  observations of governance mechanisms both in naturally evolved
  systems and in human social systems." -/

/-- A two-level governance hierarchy: an operations level regulated
    by a coordination level.

    The coordinator monitors the operations level over a longer time
    scale and modifies its set point when needed. This is the minimal
    HCGS — the pattern that repeats at every scale.

    `S_ops`: operations state space (fast dynamics)
    `S_coord`: coordination state space (slow dynamics)
    `O`: observable output type -/
structure TwoLevelGovernance (α : Type*) [ActsOn α]
    (S_ops S_coord O : Type*) where
  system : ConcreteSystem α
  opsSetPoint : O
  opsSensor : S_ops → O
  opsError : O → O → O
  opsCorrect : O → S_ops → S_ops
  coordLaw : S_coord → O → S_coord
  setPointUpdate : S_coord → O → O

/-- The operations-level homeostat at the current coordination state. -/
def TwoLevelGovernance.opsHomeostat {α : Type*} [ActsOn α]
    {S_ops S_coord O : Type*}
    (tlg : TwoLevelGovernance α S_ops S_coord O)
    (sc : S_coord) : Homeostat S_ops O where
  setPoint := tlg.setPointUpdate sc (tlg.opsError tlg.opsSetPoint tlg.opsSetPoint)
  sensor := tlg.opsSensor
  error := tlg.opsError
  correct := tlg.opsCorrect

/-- The combined two-level dynamics: coordination modifies the
    operations set point, operations corrects against it.
    This IS Mobus's feed-downward mechanism formalized. -/
def TwoLevelGovernance.combinedLaw {α : Type*} [ActsOn α]
    {S_ops S_coord O : Type*}
    (tlg : TwoLevelGovernance α S_ops S_coord O) :
    S_coord × S_ops → S_coord × S_ops :=
  fun (sc, so) =>
    let currentSetPoint := tlg.setPointUpdate sc (tlg.opsError tlg.opsSetPoint tlg.opsSetPoint)
    let err := tlg.opsError (tlg.opsSensor so) currentSetPoint
    let newOps := tlg.opsCorrect err so
    let newCoord := tlg.coordLaw sc (tlg.opsError (tlg.opsSensor so) tlg.opsSetPoint)
    (newCoord, newOps)

/-- The operations homeostat's lens at a fixed coordination state.

    At any coordination state, the operations homeostat induces a lens
    on the operations state space. The coordinator modifies WHICH lens
    is active by changing the set point — this is the additional
    governance structure that lenses alone don't capture.

    The factored relationship: lens = bidirectional channel,
    governance = channel + goal (set point). TwoLevelGovernance
    parameterizes the channel by the coordinator's state. -/
theorem TwoLevelGovernance.opsLens_eq {α : Type*} [ActsOn α]
    {S_ops S_coord O : Type*}
    (tlg : TwoLevelGovernance α S_ops S_coord O)
    (sc : S_coord) :
    (tlg.opsHomeostat sc).toLens =
      { get := tlg.opsSensor
        put := fun s o => tlg.opsCorrect
          (tlg.opsError o
            (tlg.setPointUpdate sc
              (tlg.opsError tlg.opsSetPoint tlg.opsSetPoint))) s } := by
  rfl

end Systems
