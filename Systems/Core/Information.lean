/-
  Systems/Core/Information.lean
  Principle 7: Information & Knowledge — layered, with Shannon as a bounded special case

  Mobus, Systems Science: "Systems encode knowledge and receive and send
  information." His distinction: information = received messages; knowledge =
  encoded/accumulated patterns.

  DESIGN — the architectural commitment (Klir's Generalized Information Theory):
  Shannon's communication-statistics is ONE measure in a lattice, not the genus.
  We build information in three layers, each requiring strictly MORE structure
  than the last, so that "Shannon is a special engineering case" is forced by the
  dependency graph rather than asserted:

    GENUS (relational, probability-free)
      Information = a difference that makes a difference (Bateson): a message is
      informative for a receiver iff it changes the receiver's state. Knowledge
      is the state it changes — the internal model (#9/#10) information updates.
      No probability, no measure, no distribution. This is the qualitative
      substrate.        ↑ refines by fixing a set of distinguishable states
    HARTLEY (set-based, probability-free)
      Nonspecificity = log of the number of distinguishable outcomes. Quantifies
      "how much could be resolved" with NO probability assumption (Hartley 1928,
      prior to Shannon).        ↑ refines by adding a distribution
    SHANNON (probability-based — the communication-engineering special case)
      Expected information `entropy p` (from GoodRegulator.lean). The headline
      refinement theorem `entropy_le_hartley_univ`: Shannon entropy is bounded
      ABOVE by the Hartley measure, with equality exactly at the uniform
      distribution (`entropy_uniform_eq_log_card`). Adding probabilistic
      structure can only LOWER the measure from its prob-free ceiling, and
      recovers Hartley only under maximal ignorance. That inequality is the
      precise sense in which Shannon sits *below* Hartley.

  The top of the stack is left deliberately OPEN: a semantic / viability notion
  of information (meaning, goal-relevance — refining the genus by adding a
  set-point à la Governance #8) is the research horizon, not formalized here.

  Connection to the ontology:
  - A `Channel` is a message-driven state update `recv : S → M → S`. The
    autonomous internal model (#9) is the input-free special case
    (`InternalModel.toChannel`, M = Unit): information is what makes model-update
    OPEN rather than closed — the environmental input the autonomous model lacks.
  - A non-informative message at a state is exactly an equilibrium of that
    message's action (`noninformative_iff_equilibrium`), tying the genus to
    Dynamics (#4).

  Deferred (research-level): mutual information, the data-processing inequality,
  operational channel capacity (sup of mutual information), and the semantic/
  viability layer.
-/

import Systems.Core.InternalModel
import Systems.Core.GoodRegulator
import Mathlib.Analysis.Convex.Jensen

namespace Systems

/-! ## Layer 1 — the genus: information as a difference that makes a difference

  Probability-free. A receiver is a message-driven state update; a message
  carries information iff it changes the state. Knowledge is the state. -/

/-- A channel: a receiver whose state `S` is updated by messages `M`.
    `recv s m` is the receiver's new state after receiving `m` in state `s`.
    The state IS the receiver's knowledge (Mobus: knowledge = encoded pattern);
    a message is transient (Mobus: information = received message). -/
structure Channel (S : Type*) (M : Type*) where
  /-- How a received message updates the receiver's state (knowledge). -/
  recv : S → M → S

/-- A message is **informative** for the receiver at state `s` iff it changes the
    state — Bateson's "a difference that makes a difference." This is the genus
    of information, requiring no probability or measure. -/
def Channel.Informative {S M : Type*} (c : Channel S M) (s : S) (m : M) : Prop :=
  c.recv s m ≠ s

/-- A message carries no information exactly when it leaves the state unchanged. -/
theorem Channel.noninformative_iff {S M : Type*} (c : Channel S M) (s : S) (m : M) :
    ¬ c.Informative s m ↔ c.recv s m = s := not_not

/-- The genus ties to Dynamics (#4): a non-informative message at `s` is exactly
    one for which `s` is an equilibrium of that message's action. "A difference
    that makes a difference" = "not already at the fixed point." -/
theorem Channel.noninformative_iff_equilibrium {S M : Type*}
    (c : Channel S M) (s : S) (m : M) :
    ¬ c.Informative s m ↔ IsEquilibrium (fun s' => c.recv s' m) s := not_not

/-- An internal model (#9) is the input-free channel: the receiver's only
    "message" is the trivial one, and `recv` is the model's autonomous dynamics.
    Information generalizes the internal model by adding a message input —
    closed-loop model evolution becomes open-loop, message-driven update. -/
def InternalModel.toChannel {R S : Type*} (im : InternalModel R S) : Channel R Unit where
  recv := fun r _ => im.internalDyn r

/-- For the input-free channel of an internal model, "the message is informative"
    means precisely "the model state is not at internal equilibrium" — so the
    genus of information specializes back to the dynamics of #9/#10. -/
theorem InternalModel.toChannel_informative_iff {R S : Type*}
    (im : InternalModel R S) (r : R) :
    im.toChannel.Informative r () ↔ im.internalDyn r ≠ r := Iff.rfl

/-! ## Layer 2 — Hartley nonspecificity: probability-free quantity

  The amount of potential information in a set of equally-possible distinguishable
  states is the log of their count (Hartley 1928). No distribution required. -/

/-- Hartley measure (nonspecificity) of a finite set of distinguishable outcomes:
    `log |A|`. Measured in nats here (natural log, matching `entropy`); the base
    is a unit convention (bits = log₂) and does not affect the refinement
    relations below. -/
noncomputable def hartley {α : Type*} (A : Finset α) : ℝ := Real.log A.card

/-- A single distinguishable outcome carries zero nonspecificity. -/
@[simp] theorem hartley_singleton {α : Type*} (a : α) : hartley {a} = 0 := by
  rw [hartley, Finset.card_singleton, Nat.cast_one, Real.log_one]

/-- Nonspecificity is nonnegative for any nonempty outcome set. -/
theorem hartley_nonneg {α : Type*} {A : Finset α} (hA : A.Nonempty) : 0 ≤ hartley A := by
  rw [hartley]
  exact Real.log_nonneg (by exact_mod_cast hA.card_pos)

/-! ### Genus ↔ Hartley bridge

  A channel's nonspecificity at a state is the Hartley measure of the set of
  states it can distinguish (drive to). If nothing is informative, that set is a
  singleton and nonspecificity is zero. -/

/-- The nonspecificity of a channel at a state: the Hartley measure of the set of
    distinct states it can reach from `s` via some message. This is the channel's
    structural distinguishing power — probability-free. -/
noncomputable def Channel.nonspecificity {S M : Type*} [Fintype M] [DecidableEq S]
    (c : Channel S M) (s : S) : ℝ :=
  hartley (Finset.image (fun m => c.recv s m) Finset.univ)

/-- If no message is informative at `s`, the channel resolves nothing there: its
    reachable set is `{s}` and its nonspecificity is zero. The quantitative
    Hartley measure bottoms out exactly when the qualitative genus is empty. -/
theorem Channel.nonspecificity_eq_zero_of_noninformative {S M : Type*}
    [Fintype M] [Nonempty M] [DecidableEq S] (c : Channel S M) (s : S)
    (h : ∀ m, ¬ c.Informative s m) :
    c.nonspecificity s = 0 := by
  have hconst : Finset.image (fun m => c.recv s m) (Finset.univ : Finset M) = {s} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · obtain ⟨m₀⟩ := (inferInstance : Nonempty M)
      rw [Finset.mem_image]
      exact ⟨m₀, Finset.mem_univ _, (c.noninformative_iff s m₀).mp (h m₀)⟩
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨m, _, rfl⟩ := hx
      exact (c.noninformative_iff s m).mp (h m)
  rw [Channel.nonspecificity, hconst, hartley_singleton]

/-! ## Layer 3 — Shannon as a bounded special case

  Equip the outcome set with a probability distribution and the measure becomes
  Shannon entropy (`entropy`, from GoodRegulator.lean). The headline result:
  Shannon entropy is bounded above by Hartley, with equality only at uniform. -/

/-- **Maximum entropy.** For any probability distribution on a finite (nonempty)
    type, Shannon entropy is bounded above by the Hartley measure `log (card)`.
    Proof: Jensen's inequality for the concave `negMulLog` with uniform weights.
    This is the precise content of "Shannon ≤ Hartley" — adding a distribution to
    the prob-free Hartley ceiling can only lower the information measure. -/
theorem entropy_le_log_card {Z : Type*} [Fintype Z] [Nonempty Z]
    (p : Z → ℝ) (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) :
    entropy p ≤ Real.log (Fintype.card Z) := by
  have hcard : 0 < Fintype.card Z := Fintype.card_pos
  have hne : ((Fintype.card Z : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hcard.ne'
  have hpos : (0 : ℝ) < (Fintype.card Z : ℝ) := by exact_mod_cast hcard
  have hjensen :
      ∑ i : Z, ((Fintype.card Z : ℝ)⁻¹) • Real.negMulLog (p i)
        ≤ Real.negMulLog (∑ i : Z, ((Fintype.card Z : ℝ)⁻¹) • p i) :=
    Real.concaveOn_negMulLog.le_map_sum
      (fun i _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; exact mul_inv_cancel₀ hne)
      (fun i _ => Set.mem_Ici.mpr (hp i))
  have hLHS : ∑ i : Z, ((Fintype.card Z : ℝ)⁻¹) • Real.negMulLog (p i)
      = (Fintype.card Z : ℝ)⁻¹ * entropy p := by
    rw [entropy, Finset.mul_sum]; simp only [smul_eq_mul]
  have hRHSsum : ∑ i : Z, ((Fintype.card Z : ℝ)⁻¹) • p i = (Fintype.card Z : ℝ)⁻¹ := by
    simp only [smul_eq_mul, ← Finset.mul_sum, hsum, mul_one]
  have hRHSval : Real.negMulLog ((Fintype.card Z : ℝ)⁻¹)
      = (Fintype.card Z : ℝ)⁻¹ * Real.log (Fintype.card Z) := by
    simp only [Real.negMulLog_def, Real.log_inv]; ring
  rw [hLHS, hRHSsum, hRHSval] at hjensen
  have hmul := mul_le_mul_of_nonneg_left hjensen (le_of_lt hpos)
  rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hne, one_mul, one_mul] at hmul

/-- Shannon entropy equals the Hartley measure exactly at the uniform
    distribution: `entropy (uniform) = log (card)`. Maximal ignorance is the one
    distribution that saturates the prob-free ceiling. -/
theorem entropy_uniform_eq_log_card {Z : Type*} [Fintype Z] [Nonempty Z] :
    entropy (fun _ : Z => (Fintype.card Z : ℝ)⁻¹) = Real.log (Fintype.card Z) := by
  have hcard : 0 < Fintype.card Z := Fintype.card_pos
  have hne : ((Fintype.card Z : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hcard.ne'
  rw [entropy]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.negMulLog_def, Real.log_inv]
  field_simp

/-- **The refinement, stated in Hartley terms.** Over a finite outcome type,
    Shannon entropy of any distribution is at most the Hartley nonspecificity of
    the full outcome set. Shannon sits *below* Hartley — the genus-to-measure-to-
    Shannon stack with Shannon as the strictly-more-structured special case. -/
theorem entropy_le_hartley_univ {Z : Type*} [Fintype Z] [Nonempty Z]
    (p : Z → ℝ) (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) :
    entropy p ≤ hartley (Finset.univ : Finset Z) := by
  rw [hartley, Finset.card_univ]
  exact entropy_le_log_card p hp hsum

/-- The uniform distribution maximizes Shannon entropy: every distribution has
    entropy at most that of uniform. A corollary of the two results above — the
    information-theoretic statement of "maximal ignorance is maximal entropy." -/
theorem entropy_le_entropy_uniform {Z : Type*} [Fintype Z] [Nonempty Z]
    (p : Z → ℝ) (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) :
    entropy p ≤ entropy (fun _ : Z => (Fintype.card Z : ℝ)⁻¹) := by
  rw [entropy_uniform_eq_log_card]
  exact entropy_le_log_card p hp hsum

end Systems
