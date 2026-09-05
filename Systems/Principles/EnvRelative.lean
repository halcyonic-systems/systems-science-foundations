/-
  Systems/Principles/EnvRelative.lean — the environment-relative readings of #6 and #8,
  tied to a law on a product carrier `S × E`, and the separations between them
  (decisions B, C, D of 2026-09-04).

  Companion structures: `EvolutionE` (Core/Evolution.lean), `HomeostatD`
  (Core/Governance.lean), `JointStateE` (Core/EnvState.lean). Companion predicate:
  `EvolvesByEnv` (NonDegenerate.lean), which this file shows is exactly "some `EvolutionE`
  with this step climbs and moves its environment" (`evolvesByEnv_iff_evolutionE`).

  Convention: the tied reading of Matrix.lean — one carrier `S × E`, one law
  `g : S × E → S × E`, each structure asked to exist with its dynamics equal to that law.
  The disturbance index of `HomeostatD` is identified with the environment coordinate
  (`D := E`), and a homeostat is tied to the SYSTEM half of the law only (the environment's
  own motion is not the homeostat's business; :307 speaks of disturbances, not of steering
  them).

  What is proved:
    B(ii)  `frozen_climbs_not_evolvableE`, `env_moves_but_no_climb` — the two halves of
           `EvolvableE`/`EvolvesByEnv` fail independently.
    B(iii) `redQueen_evolutionE_not_evolution` — the Red Queen is an `EvolutionE` (tied,
           climbing, environment-moving) and an `Evolution` under NO single order.
    C      `HomeostatD.Robust` — the rendering of :307/:309 for the disturbed law;
           `Homeostat.toD_robust_iff` — on the trivial disturbance it is `GovernsNeg`'s
           feedback clause.
    D(i)   `sep_governanceD_evolutionE` — a robust, effective disturbed homeostat whose
           step is NOT selection relative to the environment's declared order. With the
           fitness family left free the same law IS `EvolvesByEnv` (`evolvesByEnv_settle`);
           that is the `evolvesBy_of_governs` finding of Matrix.lean again, and the cell
           is only separable once the environment's order is data rather than a choice.
    D(ii)  `sep_evolutionE_governanceD` — the Red Queen is not the system half of any
           robust, effective disturbed homeostat, for any set point: no state is held.

  Every theorem's `#print axioms` profile is recorded in its docstring and re-emitted at
  the end of the file; none uses `sorryAx`.
-/
import Systems.Principles.NonDegenerate
import Systems.Core.EnvState

namespace Systems

/-! ## `EvolutionE` is the structure behind `EvolvesByEnv` -/

/-- `EvolvesByEnv g` (NonDegenerate.lean) is exactly: some `EvolutionE` has `g` as its step,
    climbs somewhere, and moves its environment somewhere. `#print axioms`: none. -/
theorem evolvesByEnv_iff_evolutionE {S E : Type*} (g : S × E → S × E) :
    EvolvesByEnv g ↔ ∃ ev : EvolutionE S E, ev.step = g ∧ ev.Climbs ∧ ev.EnvMoves := by
  constructor
  · rintro ⟨fit, hsel, hclimb, hmove⟩
    exact ⟨⟨fit, g, hsel⟩, rfl, hclimb, hmove⟩
  · rintro ⟨ev, rfl, hclimb, hmove⟩
    exact ⟨ev.fit, ev.selects, hclimb, hmove⟩

/-- The Red Queen as an `EvolutionE`: fitness in environment `e` is `matchOrder e`, the step
    is `redQueen`. -/
def redQueenE : EvolutionE Bool Bool where
  fit := matchOrder
  step := redQueen
  selects := fun _ _ _ => rfl

/-- **B(iii). The Red Queen is an `EvolutionE` and not an `Evolution`.** Tied to `redQueen`:
    `redQueenE` climbs (at `(false, true)`) and moves its environment (at `(false, false)`),
    so `EvolvableE Bool Bool` is witnessed by the law itself; and under no single preorder on
    `Bool × Bool` is `redQueen` the step of an `Evolution` with a strict climb (every point is
    periodic, `redQueen_evolvesByEnv_not_evolvesBy`). Running to stay in place is new
    content. `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem redQueen_evolutionE_not_evolution :
    (redQueenE.step = redQueen ∧ redQueenE.Climbs ∧ redQueenE.EnvMoves) ∧
      EvolvableE Bool Bool ∧ ¬ EvolvesBy redQueen := by
  obtain ⟨ev, hstep, hclimb, hmove⟩ :=
    (evolvesByEnv_iff_evolutionE redQueen).mp redQueen_evolvesByEnv_not_evolvesBy.1
  refine ⟨⟨rfl, ?_, ?_⟩, ⟨ev, hclimb, hmove⟩, redQueen_evolvesByEnv_not_evolvesBy.2⟩
  · exact ⟨false, true, ⟨fun h => absurd h Bool.false_ne_true,
      fun h => Bool.false_ne_true (h rfl)⟩⟩
  · exact ⟨false, false, by decide⟩

/-! ## B(ii): the two clauses of `EvolvableE` fail independently -/

/-- The collapse to `true` with a frozen environment, as a law on `Bool × Unit`. -/
def frozenCollapse : Bool × Unit → Bool × Unit := fun p => (true, p.2)

/-- **A climb with no environment change is not `EvolvableE`.** `Bool` is `Evolvable` under
    its order (there is a strict pair), the frozen collapse is a tied blind `Evolution`
    (`evolvesBy_collapse`), `Bool × Unit` is not `EvolvableE` (nothing to move to), and no
    `EvolutionE` with the frozen collapse as step both climbs and moves its environment
    (`envEvolves_needs_env_change`). `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem frozen_climbs_not_evolvableE :
    Evolvable Bool ∧ EvolvesBy (fun _ : Bool => true) ∧ ¬ EvolvableE Bool Unit ∧
      ¬ ∃ ev : EvolutionE Bool Unit, ev.step = frozenCollapse ∧ ev.Climbs ∧ ev.EnvMoves :=
  ⟨(evolvable_iff_exists_lt' Bool).mpr envEvolves_needs_env_change.1,
    envEvolves_needs_env_change.2.1, not_evolvableE_unit Bool,
    fun h => envEvolves_needs_env_change.2.2 ((evolvesByEnv_iff_evolutionE _).mpr h)⟩

/-- The double toggle: system and environment both flip every tick. -/
def doubleToggle : Bool × Bool → Bool × Bool := fun p => (!p.1, !p.2)

/-- **An environment change with no climb is not `EvolvableE` either (tied).** The order has
    a strict pair and every `EvolutionE` with the double toggle as step moves its environment
    everywhere, yet none of them climbs (`envEvolves_needs_climb`). The carrier-level
    `EvolvableE Bool Bool` still holds (`evolvableE_of_pairs`): the content is in the tie.
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem env_moves_but_no_climb :
    (∃ s t : Bool, s < t) ∧
      (∀ ev : EvolutionE Bool Bool, ev.step = doubleToggle → ev.EnvMoves) ∧
      (¬ ∃ ev : EvolutionE Bool Bool, ev.step = doubleToggle ∧ ev.Climbs) ∧
      EvolvableE Bool Bool := by
  refine ⟨envEvolves_needs_climb.1, fun ev hstep => ⟨false, false, by rw [hstep]; decide⟩,
    ?_, evolvableE_of_pairs ⟨false, true, by decide⟩ ⟨false, true, by decide⟩⟩
  rintro ⟨ev, hstep, hclimb⟩
  exact envEvolves_needs_climb.2
    ((evolvesByEnv_iff_evolutionE _).mpr ⟨ev, hstep, hclimb, false, false, by rw [hstep]; decide⟩)

/-! ## C: robustness against disturbance -/

/-- Mobus (2022, 12-governance-model.md:307): feedback serves "to maintain an output
    function in a viable or nominal value range in the face of disturbances that might
    otherwise cause the output to deviate from a desired value."
    Mobus (2022, 12-governance-model.md:309): "an actuator ... changes the internal
    operations of the work process in opposition to the error."
    Rendering, on a linearly ordered output: for EVERY disturbance and every state, if the
    disturbed state is off target, the corrected state's sensed output lies strictly toward
    the set point from the disturbed output, on the same side (`Toward`, NonDegenerate.lean).
    "In the face of disturbances" is the universal quantifier over `D`; "maintain ... in a
    viable range" is read as "never farther than the disturbance left it, and strictly
    nearer" — the band itself is not encoded. The strict form is chosen (over "no farther")
    so that a homeostat that does nothing is not robust. -/
def HomeostatD.Robust {S O D : Type*} [LinearOrder O] (h : HomeostatD S O D) : Prop :=
  ∀ d s, ¬ h.atTarget (h.disturb d s) →
    Toward h.setPoint (h.sensor (h.disturb d s)) (h.sensor (h.feedbackLawD d s))

/-- On the trivial disturbance, robustness is exactly the negative-feedback clause of
    `GovernsNeg`: every off-target state is corrected strictly toward the set point.
    `#print axioms`: propext, Classical.choice, Quot.sound (from `Toward`'s order). -/
theorem Homeostat.toD_robust_iff {S O : Type*} [LinearOrder O] (h : Homeostat S O) :
    h.toD.Robust ↔ ∀ s, ¬ h.atTarget s → Toward h.setPoint (h.sensor s) (h.sensor (h.feedbackLaw s)) :=
  ⟨fun hr s hs => hr () s hs, fun hr _ s hs => hr s hs⟩

/-- #8 with disturbance, tied to the SYSTEM half of a law `g` on `S × E` (disturbance index
    `D := E`): some `HomeostatD` on a linearly ordered output has `(g (s, e)).1` as its
    disturbed law, is neutral at its set point (the two hypotheses of
    `Homeostat.target_is_equilibrium`), is robust, and is effective (some disturbed
    off-target state is corrected onto target in one tick). The `GovernsNeg` of the
    disturbed setting. -/
def GovernsD {S E : Type*} (g : S × E → S × E) : Prop :=
  ∃ (O : Type) (inst : LinearOrder O) (h : HomeostatD S O E),
    (∀ s e, (g (s, e)).1 = h.feedbackLawD e s) ∧
    (∀ o, h.error o o = h.error h.setPoint h.setPoint) ∧
    (∀ s', h.correct (h.error h.setPoint h.setPoint) s' = s') ∧
    @HomeostatD.Robust S O E inst h ∧
    (∃ s e, ¬ h.atTarget (h.disturb e s) ∧ h.atTarget (h.feedbackLawD e s))

/-! ## D(i): a disturbed homeostat is not selection relative to the environment's order -/

/-- The settling law: whatever the environment does to the state, the system returns to
    `false`; the environment itself toggles. -/
def settle : Bool × Bool → Bool × Bool := fun p => (false, !p.2)

/-- The homeostat behind `settle`: the disturbance `e` pushes the state to `e`; the sensor
    reads the state; set point `false`; any error is corrected onto `false` in one tick. -/
def settleHomeostat : HomeostatD Bool Bool Bool where
  setPoint := false
  sensor := id
  error := fun o p => o != p
  correct := fun err s => if err then false else s
  disturb := fun e _ => e

/-- `settle` is governed with disturbance: `settleHomeostat` is neutral, robust (the only
    off-target disturbed state is `true`, corrected onto `false`, strictly toward), and
    effective. `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem governsD_settle : GovernsD settle := by
  refine ⟨Bool, inferInstance, settleHomeostat, fun s e => ?_, fun o => ?_, fun s => rfl,
    fun d s hd => ?_, ⟨false, true, by simp [settleHomeostat, Homeostat.atTarget], rfl⟩⟩
  · cases e <;> rfl
  · cases o <;> rfl
  · cases d
    · exact absurd rfl hd
    · simp [settleHomeostat, HomeostatD.feedbackLawD, Toward]

/-- **D(i). Governance with disturbance is not evolution relative to the environment's
    declared order.** Let the environment rank the set point `false` LOWEST in every
    environment (`Bool`'s own order, `false < true`, constant in `e`). `settle` is governed
    with disturbance (`governsD_settle`), yet no `EvolutionE` with that fitness family has
    `settle` as its step: at `(true, e)` selection would need `true ≤ false`. The homeostat
    descends to its set point regardless of what the environment calls fit.
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem sep_governanceD_evolutionE :
    GovernsD settle ∧
      ¬ ∃ ev : EvolutionE Bool Bool,
        ev.fit = (fun _ => (inferInstance : Preorder Bool)) ∧ ev.step = settle := by
  refine ⟨governsD_settle, ?_⟩
  rintro ⟨ev, hfit, hstep⟩
  have h := ev.selects true true
  rw [hfit, hstep] at h
  exact absurd h (by decide)

/-- STILL DERIVABLE with the fitness family free: `settle` IS `EvolvesByEnv`, by choosing
    "the set point is fittest" (`matchOrder false`) in every environment — selection is the
    descent, the climb is at `true`, and the environment toggles. This is Matrix.lean's
    `evolvesBy_of_governs` finding surviving the environment: when the fitness order is a
    choice, governance is a special case of evolution; D(i) separates only once the
    environment's order is data. Whether SOME `GovernsD` law fails `EvolvesByEnv` outright
    is left open here. `#print axioms`: none. -/
theorem evolvesByEnv_settle : EvolvesByEnv settle := by
  refine ⟨fun _ => matchOrder false, fun s e h => rfl, ⟨true, false, ?_⟩,
    ⟨false, false, by decide⟩⟩
  exact ⟨fun h => absurd h (by decide), fun h => absurd (h rfl) (by decide)⟩

/-! ## D(ii): the Red Queen holds no state -/

/-- **D(ii). Environment-relative evolution is not governance with disturbance.** The Red
    Queen's system half is `(s, e) ↦ e`. Suppose it were the disturbed law of a neutral,
    robust, effective homeostat with set point `p`. Effectiveness gives an environment `e₀`
    at target (`sensor e₀ = p`) whose disturbance lands off target, hence on `e₁ := !e₀`, and
    the correction of that disturbed state is `e₀`. Now run the law in environment `e₁`:
    its disturbance lands on `e₁` or on `e₀`. On `e₁` (off target), robustness demands the
    correction — which the law says is `e₁` itself — lie strictly nearer the set point than
    `e₁`: impossible. On `e₀` (at target), neutrality fixes the correction at `e₀`, but the
    law says `e₁`. No set point, sensor, or correction survives: the Red Queen holds nothing.
    Together with `redQueen_evolutionE_not_evolution`, the two structures are separated on
    the common carrier `Bool × Bool` in both directions.
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem sep_evolutionE_governanceD :
    (redQueenE.step = redQueen ∧ redQueenE.Climbs ∧ redQueenE.EnvMoves) ∧
      ¬ GovernsD redQueen := by
  refine ⟨redQueen_evolutionE_not_evolution.1, ?_⟩
  rintro ⟨O, inst, h, hlaw, -, hn, hrob, s₀, e₀, hoff, hon⟩
  have hl : ∀ s e, h.feedbackLawD e s = e := fun s e => (hlaw s e).symm
  rw [hl] at hon
  generalize hx : h.disturb e₀ s₀ = x at hoff
  have hxe : x ≠ e₀ := fun heq => hoff (heq ▸ hon)
  have key : h.feedbackLawD e₀ s₀ = e₀ := hl s₀ e₀
  have hbool : ∀ a b c : Bool, a ≠ b → c ≠ a → c = b := by decide
  by_cases hy : h.disturb x s₀ = x
  · have hr := hrob x s₀ (by rw [hy]; exact hoff)
    rw [hl s₀ x, hy] at hr
    unfold Homeostat.atTarget at hoff
    rcases lt_or_gt_of_ne hoff with h1 | h1
    · exact lt_irrefl _ (hr.1 h1).1
    · exact lt_irrefl _ (hr.2 h1).1
  · have hy' : h.disturb x s₀ = e₀ := hbool x e₀ _ hxe hy
    have hl2 : h.feedbackLawD x s₀ = x := hl s₀ x
    unfold HomeostatD.feedbackLawD at hl2
    rw [hy'] at hl2
    unfold Homeostat.atTarget at hon
    rw [hon, hn] at hl2
    exact hxe hl2.symm

/-! ## Axiom profiles (kernel output, recorded in each docstring) -/

#print axioms evolvesByEnv_iff_evolutionE
#print axioms redQueen_evolutionE_not_evolution
#print axioms frozen_climbs_not_evolvableE
#print axioms env_moves_but_no_climb
#print axioms Homeostat.toD_robust_iff
#print axioms governsD_settle
#print axioms sep_governanceD_evolutionE
#print axioms evolvesByEnv_settle
#print axioms sep_evolutionE_governanceD
#print axioms Evolution.freeze_not_envMoves
#print axioms not_evolvableE_unit
#print axioms evolvable_iff_frozen_climbs
#print axioms evolvableE_of_pairs
#print axioms HomeostatD.feedbackLawD_eq
#print axioms Homeostat.toD_toHomeostat
#print axioms Homeostat.toD_feedbackLawD
#print axioms HomeostatD.toHomeostat_toD
#print axioms envState_subsingleton_of_closed

end Systems
