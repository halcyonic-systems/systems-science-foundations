/-
  Systems/Principles/NonDegenerate.lean — the proposed non-degeneracy conditions, applied
  as NEW predicates over the existing state-block structures (no structure is altered).

  Companion: docs/paper/independence-matrix.md, "Proposed non-degeneracy conditions" and
  the vacuity ledger. Convention: the tied reading of Matrix.lean (one carrier, one law,
  each structure asked to exist with its dynamics equal to that law).

  The four strengthenings and the sentence each is meant to say:

    `GovernsNeg f`      Governance.lean, `Not encoded:` "in opposition to the error"
                        (Mobus 12-governance-model:309). Rendering: an ordered output type;
                        at every off-target state the corrected sensed value lies strictly
                        closer to the set point, on the same side (`Toward`). Direction is
                        the sentence; the no-crossing clause is a choice, documented below.
    `UnderstoodNC f`    Understanding.lean: `modelDyn` non-constant — the model predicts
                        something that changes. This tightens an ENCODED line ("make
                        predictions", :374), not a `Not encoded:` line; see the report.
    `DirectedThroughModel f`
                        Improvability.lean: the intervention factors through `abstract`.
                        Shown VACUOUS here (`directedThroughModel_iff_directed`): the
                        constant map factors through every abstraction. The reading that
                        bites is `DirectedUnderModel` (the intervened law is still tracked
                        by the SAME model dynamics): witnessed and separated below.
    `EvolvesByEnv g`    Evolution.lean, `Not encoded:` "long-term changes in their
                        environments" (the preorder is fixed). Rendering: a product carrier
                        `S × E`, a family `fit : E → Preorder S` (M&K: fitness "has no
                        meaning without considering a system's environment"), selection
                        relative to the CURRENT environment, a strict climb somewhere, and
                        an environment that itself moves somewhere.

  Why `JointState` is imported but not used as the carrier: `JointState` takes the product
  over `composition` only (JointState.lean, `JointState`), so `environment` things carry no
  coordinate. An environment that changes cannot ride on it without changing that
  definition. `CoupledDynamicSystem` (Dynamics.lean) already provides the two-factor product,
  and `EvolvesByEnv` is stated on its `combinedLaw` shape.

  Every theorem's `#print axioms` profile is recorded in its docstring and re-emitted at the
  end of the file; none uses `sorryAx`.
-/
import Systems.Principles.Matrix
import Systems.Core.JointState

namespace Systems

/-! ## #8 with negative feedback -/

/-- `b` is strictly closer to `p` than `a` is, on the same side of `p` (for `a ≠ p`; at
    `a = p` both clauses are vacuous). This is "the actuator changes the internal operations
    of the work process in opposition to the error": the error `a - p` has one sign, the
    correction moves against it. The `b ≤ p` / `p ≤ b` clauses forbid crossing the set point
    in one tick — a choice, made so that "opposition" cannot be satisfied by an overshoot
    that lands on the far side; drop them and `Toward` is the bare direction condition. -/
def Toward {O : Type*} [LinearOrder O] (p a b : O) : Prop :=
  (a < p → a < b ∧ b ≤ p) ∧ (p < a → b < a ∧ p ≤ b)

/-- #8 strengthened: `Governs f` (neutral at the set point, effective somewhere) on a
    linearly ordered output type, plus negative feedback at EVERY off-target state: the
    sensed value after correction lies strictly toward the set point. Mobus's sentence is
    universal ("If a disturbance ... causes the value to vary from an ideal ... either higher
    or lower, an error signal is generated"), so the feedback clause is universal. -/
def GovernsNeg {S : Type*} (f : S → S) : Prop :=
  ∃ (O : Type) (inst : LinearOrder O) (h : Homeostat S O), h.feedbackLaw = f ∧
    (∀ o, h.error o o = h.error h.setPoint h.setPoint) ∧
    (∀ s', h.correct (h.error h.setPoint h.setPoint) s' = s') ∧
    (∃ s, ¬ h.atTarget s ∧ h.atTarget (f s)) ∧
    (∀ s, ¬ h.atTarget s → @Toward O inst h.setPoint (h.sensor s) (h.sensor (f s)))

/-- `GovernsNeg` refines `Governs`: drop the order and the feedback clause.
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem governsNeg_governs {S : Type*} {f : S → S} (h : GovernsNeg f) : Governs f :=
  match h with
  | ⟨O, _, h, hlaw, hz, hn, heff, _⟩ => ⟨O, h, hlaw, hz, hn, heff⟩

/-- Under neutrality, a state at target is fixed by the law (the content of
    `Homeostat.target_is_equilibrium`, restated on the tied law). `#print axioms`: none. -/
theorem GovernsNeg.fixed_of_atTarget {S O : Type*} {f : S → S} (h : Homeostat S O)
    (hlaw : h.feedbackLaw = f)
    (hz : ∀ o, h.error o o = h.error h.setPoint h.setPoint)
    (hn : ∀ s', h.correct (h.error h.setPoint h.setPoint) s' = s')
    {s : S} (hs : h.atTarget s) : f s = s := by
  have := h.target_is_equilibrium s hs hz hn
  rwa [hlaw] at this

/-- A law with a 2-cycle `a ↔ b` has no negative feedback: neither `a` nor `b` is at target
    (a target state is fixed), so each correction must land strictly closer to the set point
    than the other, on the same side — impossible both ways. This is the honest content of
    "in opposition to the error": an oscillation is not opposition.
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem not_governsNeg_of_two_cycle {S : Type*} {f : S → S} {a b : S} (hab : a ≠ b)
    (ha : f a = b) (hb : f b = a) : ¬ GovernsNeg f := by
  rintro ⟨O, inst, h, hlaw, hz, hn, -, hneg⟩
  have hna : ¬ h.atTarget a := fun hs =>
    hab (by rw [← GovernsNeg.fixed_of_atTarget h hlaw hz hn hs, ha])
  have hnb : ¬ h.atTarget b := fun hs =>
    hab (by rw [← GovernsNeg.fixed_of_atTarget h hlaw hz hn hs, hb])
  have t1 := hneg a hna
  have t2 := hneg b hnb
  rw [ha] at t1
  rw [hb] at t2
  unfold Homeostat.atTarget at hna hnb
  rcases lt_or_gt_of_ne hna with h1 | h1
  · obtain ⟨h2, h3⟩ := t1.1 h1
    rcases lt_or_gt_of_ne hnb with h4 | h4
    · exact absurd (t2.1 h4).1 (not_lt.mpr h2.le)
    · exact absurd h3 (not_le.mpr h4)
  · obtain ⟨h2, h3⟩ := t1.2 h1
    rcases lt_or_gt_of_ne hnb with h4 | h4
    · exact absurd h3 (not_le.mpr h4)
    · exact absurd (t2.2 h4).1 (not_lt.mpr h2.le)

/-- The collapse onto a point `c` from a carrier with a second point governs with negative
    feedback: sensor "am I off `c`?" into `Bool` (`false < true`), set point `false`, every
    off-target state corrected onto `c` in one tick — strictly toward, same side. The
    one-tick homeostat. `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem governsNeg_const {S : Type*} [DecidableEq S] (c d : S) (hcd : d ≠ c) :
    GovernsNeg (fun _ : S => c) := by
  refine ⟨Bool, inferInstance,
    ⟨false, fun s => decide (s ≠ c), fun o p => (o != p), fun e s => if e then c else s⟩,
    ?_, ?_, ?_, ⟨d, ?_, ?_⟩, ?_⟩
  · funext s
    by_cases hs : s = c <;> simp [Homeostat.feedbackLaw, hs]
  · intro o; cases o <;> rfl
  · intro s; rfl
  · simp [Homeostat.atTarget, hcd]
  · simp [Homeostat.atTarget]
  · intro s hs
    simp only [Homeostat.atTarget, decide_eq_false_iff_not, not_not] at hs
    simp [Toward, hs]

/-! ## #11 and #12 with a model that tracks something -/

/-- The model dynamics is not constant: the model predicts at least one change. -/
def Understanding.Nonconstant {S M : Type*} (u : Understanding S M) : Prop :=
  ∃ m₁ m₂, u.modelDyn m₁ ≠ u.modelDyn m₂

/-- #11 strengthened: some understanding of `f` has non-constant model dynamics. Excludes
    `Understanding.ofMissingPoint` (model dynamics `const false`). -/
def UnderstoodNC {S : Type*} (f : S → S) : Prop :=
  ∃ (M : Type) (u : Understanding S M), u.systemDyn = f ∧ u.Nonconstant

/-- #12 (full) strengthened: some directed agent on `f` whose understanding has non-constant
    model dynamics. -/
def DirectedNC {S : Type*} (f : S → S) : Prop :=
  ∃ (M : Type) (a : DirectedAgent S M), a.understanding.systemDyn = f ∧
    a.understanding.Nonconstant

/-- `#print axioms`: none. -/
theorem understood_of_understoodNC {S : Type*} {f : S → S} (h : UnderstoodNC f) :
    Understood f := by
  obtain ⟨M, u, hu, -⟩ := h
  exact ⟨M, u, hu⟩

/-- `#print axioms`: none. -/
theorem understoodNC_of_directedNC {S : Type*} {f : S → S} (h : DirectedNC f) :
    UnderstoodNC f := by
  obtain ⟨M, a, ha, hnc⟩ := h
  exact ⟨M, a.understanding, ha, hnc⟩

/-- The abstraction of an understanding is never constant (surjective onto a nontrivial
    model). `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem Understanding.abstract_not_const {S M : Type*} (u : Understanding S M)
    (h : ∀ x y, u.abstract x = u.abstract y) : False := by
  haveI := u.nontrivial
  obtain ⟨m₁, m₂, hm⟩ := exists_pair_ne M
  obtain ⟨x₁, rfl⟩ := u.surjective m₁
  obtain ⟨x₂, rfl⟩ := u.surjective m₂
  exact hm (h x₁ x₂)

/-- **The star collapse is never understood non-degenerately, on any carrier.** If the law is
    `const c`, every understanding's model dynamics is the constant `abstract c` on the whole
    model (by `abstracts` and surjectivity). The one-tick homeostat that lands everything on
    its set point leaves the model nothing to predict but "we are at the set point".
    `#print axioms`: none. -/
theorem not_understoodNC_const {S : Type*} (c : S) : ¬ UnderstoodNC (fun _ : S => c) := by
  rintro ⟨M, u, hu, m₁, m₂, hne⟩
  obtain ⟨x₁, rfl⟩ := u.surjective m₁
  obtain ⟨x₂, rfl⟩ := u.surjective m₂
  have h₁ := u.abstracts x₁
  have h₂ := u.abstracts x₂
  rw [hu] at h₁ h₂
  exact hne (h₁.symm.trans h₂)

/-- `#print axioms`: none. -/
theorem not_directedNC_const {S : Type*} (c : S) : ¬ DirectedNC (fun _ : S => c) :=
  fun h => not_understoodNC_const c (understoodNC_of_directedNC h)

/-! ### Non-vacuity of the NC predicates -/

/-- The 4-cycle is understood by parity, and parity toggles: non-constant.
    `#print axioms`: propext. -/
theorem understoodNC_rotation : UnderstoodNC (fun s : Fin 4 => s + 1) :=
  ⟨Bool, rotationUnderstanding, rfl, true, false, by decide⟩

/-- The parity agent on the 4-cycle is a non-degenerately directed agent.
    `#print axioms`: propext. -/
theorem directedNC_rotation : DirectedNC (fun s : Fin 4 => s + 1) :=
  ⟨Bool, rotationAgent, rfl, true, false, by decide⟩

/-- The library's own example, `noisyPairUnderstanding` (`modelDyn := id` on `Bool`), is
    non-constant. `#print axioms`: none. -/
theorem understoodNC_noisyPair : UnderstoodNC noisyPairUnderstanding.systemDyn :=
  ⟨Bool, noisyPairUnderstanding, rfl, true, false, by decide⟩

/-! ## #12 with the intervention constrained through the model -/

/-- #12 (full) with the intervention factoring through the abstraction: the agent chooses
    the next state from what it sees (`intervene dyn = φ ∘ abstract`). This is the reading
    the brief suggested; it is shown vacuous just below. -/
def DirectedThroughModel {S : Type*} (f : S → S) : Prop :=
  ∃ (M : Type) (a : DirectedAgent S M), a.understanding.systemDyn = f ∧
    ∃ φ : M → S, a.intervene a.understanding.systemDyn = φ ∘ a.understanding.abstract

/-- **Factoring through the model is no constraint.** The pinning intervention
    `fun _ => const goal` factors through every abstraction (`φ := const goal`), so every
    directed agent can be replaced by one whose intervention factors. The "drive straight to
    the goal" vacuity of `improved_iff_moving` survives this reading intact.
    `#print axioms`: none. -/
theorem directedThroughModel_iff_directed {S : Type*} (f : S → S) :
    DirectedThroughModel f ↔ Directed f := by
  constructor
  · rintro ⟨M, a, ha, -⟩
    exact ⟨M, a, ha⟩
  · rintro ⟨M, a, ha⟩
    let a' : DirectedAgent S M :=
      { understanding := a.understanding
        goal := a.goal
        intervene := fun _ => Function.const S a.goal
        improves := rfl
        genuine := a.genuine }
    exact ⟨M, a', ha, Function.const M a.goal, rfl⟩

/-- STILL DERIVABLE (#12 ⇏ #4 with `DirectedThroughModel`): strengthening the SOURCE cannot
    remove a derivation; `genuine` still names a moving state. `#print axioms`: none. -/
theorem moving_of_directedThroughModel {S : Type*} {f : S → S} (h : DirectedThroughModel f) :
    Moving f :=
  moving_of_directed ((directedThroughModel_iff_directed f).mp h)

/-- The reading that bites: the intervened law is still tracked by the SAME model dynamics —
    `abstract ∘ intervene dyn = modelDyn ∘ abstract`. The agent changes only what its model
    cannot see; every prediction the understanding made survives the intervention. This is
    "only changes dynamics up to the model's resolution" read literally. -/
def DirectedUnderModel {S : Type*} (f : S → S) : Prop :=
  ∃ (M : Type) (a : DirectedAgent S M), a.understanding.systemDyn = f ∧
    ∀ s, a.understanding.abstract (a.intervene a.understanding.systemDyn s) =
      a.understanding.modelDyn (a.understanding.abstract s)

/-- An under-model agent's goal sits in a fibre whose model state is a model rest state:
    `improves` plus tracking force `modelDyn (abstract goal) = abstract goal`.
    `#print axioms`: none. -/
theorem DirectedUnderModel.goal_model_fixed {S M : Type*} (a : DirectedAgent S M)
    (htrack : ∀ s, a.understanding.abstract (a.intervene a.understanding.systemDyn s) =
      a.understanding.modelDyn (a.understanding.abstract s)) :
    a.understanding.modelDyn (a.understanding.abstract a.goal) =
      a.understanding.abstract a.goal := by
  have h := htrack a.goal
  have hi : a.intervene a.understanding.systemDyn a.goal = a.goal := a.improves
  rw [hi] at h
  exact h.symm

/-- **Understood ∧ Moving ∧ Directed ⇏ DirectedUnderModel.** The 4-cycle is understood
    (parity), moves, and admits a directed agent (`rotationAgent`), but no agent acting
    under its model: any understanding of the 4-cycle has `abstract (g+1) = abstract g` as
    soon as one model state is fixed, hence `abstract` constant on the cycle, contradicting
    `nontrivial`. This is the one place a through-model constraint separates anything: the
    only thing an agent can do to a cycle is break it, and breaking it changes what the
    model sees. `#print axioms`: propext. -/
theorem rotation_not_directedUnderModel :
    Understood (fun s : Fin 4 => s + 1) ∧ Moving (fun s : Fin 4 => s + 1) ∧
      Directed (fun s : Fin 4 => s + 1) ∧ ¬ DirectedUnderModel (fun s : Fin 4 => s + 1) := by
  refine ⟨⟨Bool, rotationUnderstanding, rfl⟩, ⟨0, by decide⟩, ⟨Bool, rotationAgent, rfl⟩, ?_⟩
  rintro ⟨M, a, ha, htrack⟩
  have hfix := DirectedUnderModel.goal_model_fixed a htrack
  have hstep : ∀ x : Fin 4,
      a.understanding.abstract (x + 1) = a.understanding.modelDyn (a.understanding.abstract x) := by
    intro x
    have e := a.understanding.abstracts x
    rw [show a.understanding.systemDyn x = x + 1 from congrFun ha x] at e
    exact e
  have h1 : a.understanding.abstract (a.goal + 1) = a.understanding.abstract a.goal := by
    rw [hstep, hfix]
  have c2 : ∀ g : Fin 4, g + 2 = g + 1 + 1 := by decide
  have c3 : ∀ g : Fin 4, g + 3 = g + 2 + 1 := by decide
  have h2 : a.understanding.abstract (a.goal + 2) = a.understanding.abstract a.goal := by
    rw [c2, hstep, h1, hfix]
  have h3 : a.understanding.abstract (a.goal + 3) = a.understanding.abstract a.goal := by
    rw [c3, hstep, h2, hfix]
  have cover : ∀ g x : Fin 4, x = g ∨ x = g + 1 ∨ x = g + 2 ∨ x = g + 3 := by decide
  have hall : ∀ x, a.understanding.abstract x = a.understanding.abstract a.goal := by
    intro x
    rcases cover a.goal x with hx | hx | hx | hx <;> rw [hx]
    · exact h1
    · exact h2
    · exact h3
  exact a.understanding.abstract_not_const fun x y => (hall x).trans (hall y).symm

/-- Non-vacuity: on the noisy pair, the agent that fixes the noisy coordinate to `true`
    without touching the conserved one acts under its model (`abstract = fst` sees the same
    identity dynamics before and after) and its intervention factors through `abstract`
    (`φ b := (b, true)`). `#print axioms`: propext. -/
theorem directedUnderModel_noisyPair :
    DirectedUnderModel noisyPairUnderstanding.systemDyn ∧
      DirectedThroughModel noisyPairUnderstanding.systemDyn := by
  let a : DirectedAgent (Bool × Bool) Bool :=
    { understanding := noisyPairUnderstanding
      goal := (true, true)
      intervene := fun _ p => (p.1, true)
      improves := rfl
      genuine := by simp [IsEquilibrium, noisyPairUnderstanding] }
  exact ⟨⟨Bool, a, rfl, fun _ => rfl⟩, ⟨Bool, a, rfl, fun b => (b, true), rfl⟩⟩

/-! ## #6 with a changing environment -/

/-- #6 strengthened, on a product carrier `S × E`: a family of fitness preorders indexed by
    the environment (M&K §10.2.1.4: fitness "has no meaning without considering a system's
    environment"), such that the tied law `g` (i) never lowers fitness relative to the
    CURRENT environment, (ii) strictly climbs somewhere, and (iii) moves the environment
    somewhere ("long-term changes in their environments"). Not an `Evolution` instance:
    that structure fixes one preorder on `S`, which is exactly the `Not encoded:` line. -/
def EvolvesByEnv {S E : Type*} (g : S × E → S × E) : Prop :=
  ∃ fit : E → Preorder S,
    (∀ s e, @LE.le S (fit e).toLE s (g (s, e)).1) ∧
    (∃ s e, @LT.lt S (fit e).toLT s (g (s, e)).1) ∧
    (∃ s e, (g (s, e)).2 ≠ e)

/-- The fitness order "matching the environment `e` is fittest": `s ≤ t` iff `s = e → t = e`.
    Everything below the match is equivalent; the match sits strictly above. -/
def matchOrder (e : Bool) : Preorder Bool where
  le s t := s = e → t = e
  lt s t := (s = e → t = e) ∧ ¬ (t = e → s = e)
  le_refl _ h := h
  le_trans _ _ _ h₁ h₂ h := h₂ (h₁ h)
  lt_iff_le_not_ge _ _ := Iff.rfl

/-- The Red Queen: the organism copies the current environment, and the environment flips
    against the organism's old state. Every generation matches the environment it was
    selected in and is mismatched by the next. -/
def redQueen : Bool × Bool → Bool × Bool := fun p => (p.2, !p.1)

/-- The Red Queen as a coupled dynamic system (`law₁ s e := e`, `law₂ s e := !s`) on the stock
    component side; its `combinedLaw` is `redQueen` definitionally. -/
def redQueenCoupled : @CoupledDynamicSystem Bool (allAction Bool) Bool Bool := by
  letI := allAction Bool
  exact ⟨stockSystem, fun _ e => e, fun s _ => !s⟩

/-- `#print axioms`: propext, Classical.choice, Quot.sound (inherited from `stockSystem`). -/
theorem redQueenCoupled_combinedLaw :
    (@CoupledDynamicSystem.combinedLaw Bool (allAction Bool) Bool Bool redQueenCoupled) =
      redQueen := rfl

/-- Non-vacuity: the Red Queen evolves relative to its environment. Selection: the new state
    is the current match, the top of `matchOrder e`. Strict climb at `(false, true)`. The
    environment moves at `(false, false)`. `#print axioms`: none. -/
theorem evolvesByEnv_redQueen : EvolvesByEnv redQueen := by
  refine ⟨matchOrder, fun s e h => rfl, ⟨false, true, ?_⟩, ⟨false, false, by decide⟩⟩
  exact ⟨fun h => absurd h Bool.false_ne_true, fun h => Bool.false_ne_true (h rfl)⟩

/-- **`EvolvesByEnv` is not `EvolvesBy` on the product.** The Red Queen is a 4-cycle on
    `Bool × Bool` — every point periodic — so under NO single fitness order on the product is
    it a blind evolution (`not_evolvesBy_of_periodic`), yet relative to each current
    environment it climbs. Running to stay in place: the environment-relative reading is new
    content, not a special case of the fixed-order one.
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem redQueen_evolvesByEnv_not_evolvesBy : EvolvesByEnv redQueen ∧ ¬ EvolvesBy redQueen :=
  ⟨evolvesByEnv_redQueen, not_evolvesBy_of_periodic fun s => ⟨3, by revert s; decide⟩⟩

/-! ### The `Evolvable` vacuity does not recur

  `evolvable_iff_exists_lt'` showed `Evolvable S` is a property of the order alone. Both
  theorems below have an order with a strict pair (`false < true` on `Bool`) and a law that
  fails `EvolvesByEnv` — one because the environment never moves though the organism climbs,
  one because the organism cycles though the environment moves. The law is tied and the
  order does not decide the verdict. -/

/-- The collapse to `true` with a frozen environment: its `S`-part is a blind evolution
    (`evolvesBy_collapse`), the order has a strict pair, and `EvolvesByEnv` fails because the
    environment never changes. `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem envEvolves_needs_env_change :
    (∃ s t : Bool, s < t) ∧ EvolvesBy (fun _ : Bool => true) ∧
      ¬ EvolvesByEnv (fun p : Bool × Unit => (true, p.2)) :=
  ⟨⟨false, true, by decide⟩, evolvesBy_collapse, fun ⟨_, _, _, _, _, he⟩ => he rfl⟩

/-- The double toggle: the environment moves at every step and the order has a strict pair,
    but no environment-indexed fitness lets the organism climb — selection at `(!s, e)` gives
    `!s ≤ s` in the same environment where `s < !s` was claimed.
    `#print axioms`: none. -/
theorem envEvolves_needs_climb :
    (∃ s t : Bool, s < t) ∧ ¬ EvolvesByEnv (fun p : Bool × Bool => (!p.1, !p.2)) := by
  refine ⟨⟨false, true, by decide⟩, ?_⟩
  rintro ⟨fit, hsel, ⟨s, e, hlt⟩, -⟩
  letI := fit e
  have h₁ : @LE.le Bool (fit e).toLE (!s) s := by
    have h := hsel (!s) e
    change @LE.le Bool (fit e).toLE (!s) (!(!s)) at h
    rwa [Bool.not_not] at h
  change @LT.lt Bool (fit e).toLT s (!s) at hlt
  exact (lt_iff_le_not_ge.mp hlt).2 h₁

/-! ## The seven cells, re-run -/

/-! ### (#8 ⇏ #6) with `GovernsNeg` -/

/-- STILL DERIVABLE (#8 ⇒ #6 with `GovernsNeg`): negative feedback is still a climb onto a
    fixed point, so `evolvesBy_of_governs` fires through `governsNeg_governs`. Sharpening #8
    cannot break a derivation out of #8. What WOULD separate is a target the homeostat cannot
    reach — `EvolvesByEnv` — but that lives on `S × E` and a homeostat on `S` has no
    environment coordinate; the cell is not statable on one carrier.
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem evolvesBy_of_governsNeg {S : Type*} {f : S → S} (h : GovernsNeg f) : EvolvesBy f :=
  evolvesBy_of_governs (governsNeg_governs h)

/-! ### (#12 ⇏ #4) with `DirectedThroughModel` — see `moving_of_directedThroughModel`:
    STILL DERIVABLE, and the predicate is equivalent to `Directed` anyway. -/

/-! ### (#6 ⇏ #11), (#8 ⇏ #11), (#6 ⇏ #12), (#8 ⇏ #12) with `UnderstoodNC` / `DirectedNC`
    on `Fin 3` — the former cardinality-only cells -/

/-- The star collapse on three states: every state lands on `0` in one tick. -/
def collapse3 : Fin 3 → Fin 3 := fun _ => 0

/-- `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem governsNeg_collapse3 : GovernsNeg collapse3 :=
  governsNeg_const (0 : Fin 3) 1 (by decide)

/-- `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem evolvesBy_collapse3 : EvolvesBy collapse3 :=
  evolvesBy_of_governsNeg governsNeg_collapse3

/-- **#6 ⇏ #11 (NC), on three states.** The hypotheses of `understood_of_evolvesBy_finite`
    hold (`2 < card`, a blind evolution) and its conclusion still holds — `Understood` — but
    only through a constant model: `UnderstoodNC` fails. The separation is by dynamics, not
    cardinality, and `not_understoodNC_const` shows it holds on EVERY carrier.
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem sep_evolution_understandingNC :
    2 < Fintype.card (Fin 3) ∧ EvolvesBy collapse3 ∧ Understood collapse3 ∧
      ¬ UnderstoodNC collapse3 :=
  ⟨by decide, evolvesBy_collapse3,
    understood_of_evolvesBy_finite collapse3 (by decide) evolvesBy_collapse3,
    not_understoodNC_const 0⟩

/-- **#8 ⇏ #11 (NC), on three states.** The one-tick negative-feedback homeostat is
    understood only by the constant model "at the set point".
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem sep_governanceNeg_understandingNC :
    2 < Fintype.card (Fin 3) ∧ GovernsNeg collapse3 ∧ ¬ UnderstoodNC collapse3 :=
  ⟨by decide, governsNeg_collapse3, not_understoodNC_const 0⟩

/-- **#6 ⇏ #12 (full, NC), on three states.** `directed_of_evolvesBy_finite` still yields a
    `Directed`; no agent with a non-constant model exists.
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem sep_evolution_directedNC :
    2 < Fintype.card (Fin 3) ∧ EvolvesBy collapse3 ∧ Directed collapse3 ∧
      ¬ DirectedNC collapse3 :=
  ⟨by decide, evolvesBy_collapse3,
    directed_of_evolvesBy_finite collapse3 (by decide) evolvesBy_collapse3,
    not_directedNC_const 0⟩

/-- **#8 ⇏ #12 (full, NC), on three states.**
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem sep_governanceNeg_directedNC :
    2 < Fintype.card (Fin 3) ∧ GovernsNeg collapse3 ∧ ¬ DirectedNC collapse3 :=
  ⟨by decide, governsNeg_collapse3, not_directedNC_const 0⟩

/-- Contrast: with `DirectedThroughModel` in place of `DirectedNC` the finite derivation
    survives (the predicate is `Directed`). STILL DERIVABLE (#8 ⇒ #12 through-model on
    finite ≥ 3). `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem directedThroughModel_of_governsNeg_finite {S : Type*} [Fintype S] (f : S → S)
    (h3 : 2 < Fintype.card S) (h : GovernsNeg f) : DirectedThroughModel f :=
  (directedThroughModel_iff_directed f).mpr
    (directed_of_governs_finite f h3 (governsNeg_governs h))

/-! ### (#4 ⇏ #8) with `GovernsNeg` -/

/-- **#4 ⇏ #8 (Neg)**, same witness as before: the toggle governs nothing, a fortiori with
    negative feedback. `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem sep_dynamics_governanceNeg : Moving not ∧ ¬ GovernsNeg not :=
  ⟨sep_dynamics_governance.1, fun h => sep_dynamics_governance.2 (governsNeg_governs h)⟩

/-- Fixed point `0`, reached from `3`; `1 ↔ 2` oscillates. -/
def swapFix : Fin 4 → Fin 4 := fun x => if x = 1 then 2 else if x = 2 then 1 else 0

/-- **The strengthening is proper: `Governs ⇏ GovernsNeg`.** `swapFix` governs in the old
    sense (set point `0` held, `3` corrected onto it) but the oscillating pair `1 ↔ 2` is
    corrected in no consistent direction under any ordered sensor. The sharper form of the
    (#4 ⇏ #8) cell: a law that even governs, yet has no negative feedback.
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem sep_governance_governanceNeg : Moving swapFix ∧ Governs swapFix ∧ ¬ GovernsNeg swapFix :=
  ⟨⟨1, by decide⟩, governs_of_fixed (s := 3) (p := 0) (by decide) rfl rfl,
    not_governsNeg_of_two_cycle (a := 1) (b := 2) (by decide) rfl rfl⟩

/-! ## Axiom profiles (kernel output, recorded in each docstring) -/

#print axioms governsNeg_governs
#print axioms GovernsNeg.fixed_of_atTarget
#print axioms not_governsNeg_of_two_cycle
#print axioms governsNeg_const
#print axioms understood_of_understoodNC
#print axioms understoodNC_of_directedNC
#print axioms Understanding.abstract_not_const
#print axioms not_understoodNC_const
#print axioms not_directedNC_const
#print axioms understoodNC_rotation
#print axioms directedNC_rotation
#print axioms understoodNC_noisyPair
#print axioms directedThroughModel_iff_directed
#print axioms moving_of_directedThroughModel
#print axioms DirectedUnderModel.goal_model_fixed
#print axioms rotation_not_directedUnderModel
#print axioms directedUnderModel_noisyPair
#print axioms redQueenCoupled_combinedLaw
#print axioms evolvesByEnv_redQueen
#print axioms redQueen_evolvesByEnv_not_evolvesBy
#print axioms envEvolves_needs_env_change
#print axioms envEvolves_needs_climb
#print axioms evolvesBy_of_governsNeg
#print axioms governsNeg_collapse3
#print axioms evolvesBy_collapse3
#print axioms sep_evolution_understandingNC
#print axioms sep_governanceNeg_understandingNC
#print axioms sep_evolution_directedNC
#print axioms sep_governanceNeg_directedNC
#print axioms directedThroughModel_of_governsNeg_finite
#print axioms sep_dynamics_governanceNeg
#print axioms sep_governance_governanceNeg

end Systems
