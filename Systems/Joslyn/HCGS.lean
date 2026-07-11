/-
  Systems/Joslyn/HCGS.lean
  Phase 4.5: Control₂ ≅ HCGS — the independent convergence, machine-checked

  Joslyn (1995, from Klir/Ashby) and Mobus (citing Klir, not Joslyn)
  independently arrive at the same hierarchical control anatomy:

      Joslyn CS = ⟨C, ⟨O_E, O_I⟩⟩        Mobus HCGS (minimal, two-level)
      O_I  controlled variables      ↦   operational level (readout)
      O_E  effector/regulator        ↦   ops correction machinery
      C    source of variation       ↦   strategic CONTEXT (see below)

  CONVERGENCE (theorems 1, 2, 4): each HCGS level, taken as a perfect
  homeostat, realizes Joslyn's control₂ (`levelRealizes`, through run 4's
  `Homeostat.toControl₂Realized`); its maintained region is exactly the
  fed-down set point (`levelRealizes_stableI`); and Joslyn Def 28's
  "hierarchically distinct level ... slower time scale" (§3.3, citing
  Auger/Salthe) is the SAME claim as `TimescaleDecomposition`: packaging
  the HCGS as coupled dynamics (`toCoupled`, coherent with `combinedLaw`),
  the frozen-coordinator fast dynamics IS the level homeostat's feedback
  law (`fast_ops_is_level_homeostat` — definitional once packaged).

  DIVERGENCE (theorem 5, new — not in the roadmap): Mobus's feed-downward
  is precisely what BREAKS Joslyn's cancellation. Prop 29 demands the
  composite constraint on O_I be INVARIANT under the upper level's
  variation (`compensates`); Mobus's coordinator varies the set point in
  order to MOVE the maintained region (`feedDownward_moves_stable`). So
  the coordination level is NOT a Joslyn controller-to-be-cancelled: the
  §4.5 table maps Joslyn's C to strategic CONTEXT, and this is why —
  context (disturbance, rejected within a level) ≠ coordinator (authority,
  retunes the level's goal). Independent convergence with characterized
  divergence, the §4.7 narrative shape — here the divergence is a theorem,
  not narration.

  THE SEMANTIC GAP (documented only — deliberately NOT in types): Joslyn's
  feedback coding f : O_I → O_E is a RULE — contingent, selected,
  meaningful; it could have been otherwise, and its being followed is what
  makes the control semantic (§4 of the paper). Mobus's transforms T are
  LAWS — necessary, discovered, followed without an interpretant. Both
  sides of the isomorphism above carry the same function-shaped data, so
  the distinction rule-vs-law is invisible to the type checker; encoding
  it would require a theory of selection/interpretation the set tier does
  not have. Per the roadmap, this stays a docstring, and the isomorphism
  is STRUCTURAL only.
-/

import Systems.Joslyn.Control

namespace Systems

variable {α : Type*} [ActsOn α] {S_ops S_coord O : Type*}

/-! ## Convergence leg 1: each HCGS level realizes control₂ -/

/-- Each level of the HCGS, at any coordination state, is a homeostat
    (`opsHomeostat`) — and a PERFECT level (one whose feedback law reaches
    the fed-down set point in one tick) realizes Joslyn's control₂ through
    run 4's Governance bridge. "HCGS level = homeostat = realized
    control₂", as a composite. -/
def TwoLevelGovernance.levelRealizes [Nontrivial O]
    (tlg : TwoLevelGovernance α S_ops S_coord O) (sc : S_coord)
    (hreach : ∀ so, (tlg.opsHomeostat sc).sensor
        ((tlg.opsHomeostat sc).feedbackLaw so) =
      (tlg.opsHomeostat sc).setPoint) :
    Control₂Realized S_ops S_ops O :=
  (tlg.opsHomeostat sc).toControl₂Realized hreach

/-- The maintained region O*_I of a realized level is exactly the set point
    the coordinator issued to it — the controlled variable is pinned to the
    FED-DOWN target. Definitional: the O_I ↦ operational-readout alignment
    of the §4.5 table. -/
theorem TwoLevelGovernance.levelRealizes_stableI [Nontrivial O]
    (tlg : TwoLevelGovernance α S_ops S_coord O) (sc : S_coord)
    (hreach : ∀ so, (tlg.opsHomeostat sc).sensor
        ((tlg.opsHomeostat sc).feedbackLaw so) =
      (tlg.opsHomeostat sc).setPoint) :
    (tlg.levelRealizes sc hreach).stableI =
      {(tlg.opsHomeostat sc).setPoint} :=
  rfl

/-! ## Convergence leg 2: the timescale alignment (Joslyn Def 28) -/

/-- The HCGS as coupled dynamics: coordination (slow slot) and operations
    (fast slot) as a `CoupledDynamicSystem`. The laws are read off
    `TwoLevelGovernance.combinedLaw`'s let-bindings exactly — see
    `toCoupled_combinedLaw` for the coherence. -/
def TwoLevelGovernance.toCoupled
    (tlg : TwoLevelGovernance α S_ops S_coord O) :
    CoupledDynamicSystem α S_coord S_ops where
  system := tlg.system
  law₁ := fun sc so =>
    tlg.coordLaw sc (tlg.opsError (tlg.opsSensor so) tlg.opsSetPoint)
  law₂ := fun sc so =>
    tlg.opsCorrect
      (tlg.opsError (tlg.opsSensor so)
        (tlg.setPointUpdate sc (tlg.opsError tlg.opsSetPoint tlg.opsSetPoint)))
      so

/-- Coherence: the coupled packaging has the SAME combined dynamics as the
    two-level governance it came from. The packaging forgets nothing. -/
theorem TwoLevelGovernance.toCoupled_combinedLaw
    (tlg : TwoLevelGovernance α S_ops S_coord O) :
    tlg.toCoupled.combinedLaw = tlg.combinedLaw :=
  rfl

/-- JOSLYN DEF 28 ≡ TIMESCALE DECOMPOSITION, machine-checked: at any
    coupled equilibrium, the HCGS decomposes into fast/slow dynamics, and
    the fast operational dynamics — the coordinator frozen at its
    equilibrium value — IS the level homeostat's feedback law. Joslyn's
    "second-order variation at a hierarchically distinct level, on a
    slower time scale" (§3.3, citing Auger/Salthe) and Mobus's
    timescale-separated HCGS make the same structural claim; once both are
    packaged, the identification is definitional. -/
theorem TwoLevelGovernance.fast_ops_is_level_homeostat
    (tlg : TwoLevelGovernance α S_ops S_coord O) (sc₀ : S_coord) (so₀ : S_ops)
    (heq : CoupledEquilibrium tlg.toCoupled.law₁ tlg.toCoupled.law₂ sc₀ so₀) :
    (tlg.toCoupled.decompose sc₀ so₀ heq).fast₂ =
      (tlg.opsHomeostat sc₀).feedbackLaw :=
  rfl

/-! ## The divergence: feed-downward breaks the cancellation -/

/-- THE DIVERGENCE THEOREM (new in the sketch; not in the roadmap): if two
    coordination states issue different set points, the corresponding level
    realizations maintain DIFFERENT regions. Joslyn's Prop 29 cancellation
    demands the maintained region be invariant under the upper level's
    variation; Mobus's feed-downward exists to violate exactly that — the
    coordinator's variation MOVES O*. The upper level of the HCGS is an
    authority that retunes, not a disturbance that is cancelled: Joslyn's C
    maps to strategic CONTEXT, never to the coordinator. -/
theorem TwoLevelGovernance.feedDownward_moves_stable [Nontrivial O]
    (tlg : TwoLevelGovernance α S_ops S_coord O) {sc sc' : S_coord}
    (hreach : ∀ so, (tlg.opsHomeostat sc).sensor
        ((tlg.opsHomeostat sc).feedbackLaw so) =
      (tlg.opsHomeostat sc).setPoint)
    (hreach' : ∀ so, (tlg.opsHomeostat sc').sensor
        ((tlg.opsHomeostat sc').feedbackLaw so) =
      (tlg.opsHomeostat sc').setPoint)
    (hne : (tlg.opsHomeostat sc).setPoint ≠ (tlg.opsHomeostat sc').setPoint) :
    (tlg.levelRealizes sc hreach).stableI ≠
      (tlg.levelRealizes sc' hreach').stableI := by
  intro heq
  have hmem : (tlg.opsHomeostat sc).setPoint ∈
      (tlg.levelRealizes sc hreach).stableI := rfl
  rw [heq, tlg.levelRealizes_stableI sc' hreach'] at hmem
  exact hne hmem

end Systems
