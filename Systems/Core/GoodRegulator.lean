/-
  Systems/Core/GoodRegulator.lean
  Principle 8/9 bridge: the Conant-Ashby "Good Regulator" theorem (1970), the
  information-theoretic version.

  Conant & Ashby, "Every good regulator of a system must be a model of that
  system," Int. J. Systems Science 1(2):89-97 (1970).

  The structural skeleton (a regulator-to-system homomorphism) lives in Lens.lean
  (`ConantAshbySkeleton`) and the simulation core in InternalModel.lean. This file
  formalizes the ACTUAL theorem, which is information-theoretic:

    Setup: a reguland S, regulator R, outcomes Z, an outcome map ψ : R × S → Z,
    a fixed distribution p(S), and a regulator as a conditional p(R | S). The
    outcome distribution p(Z) follows. "Successful regulation" = H(Z) minimal.

    Theorem: the simplest optimal regulator is a deterministic mapping h : S → R —
    the regulator's action is a function of the system state, i.e. a *model* of it.

  The whole force of the proof is one entropy fact (Conant-Ashby's lemma): for an
  H(Z)-minimal regulator, for each s all positive-probability responses map to a
  SINGLE outcome — because otherwise you could shift outcome mass to make p(Z)
  more unequal, and increasing imbalance STRICTLY LOWERS entropy. That entropy
  fact is the strict (Schur-)concavity of `negMulLog`. This file proves that
  engine first (`negMulLog_transfer`), then the determinism conclusion.

  Faithfulness note: the engine below is the exact mechanism Conant-Ashby invoke
  ("any such increase in imbalance in p(Z) necessarily decreases H(Z)"). We build
  it from `Real.strictConcaveOn_negMulLog`, not by assuming the conclusion.
-/

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Systems

open Real Finset

/-! ## Finite Shannon entropy

  `entropy q = ∑ z, negMulLog (q z) = -∑ z, q z · log (q z)` for an outcome
  distribution `q : Z → ℝ` over a finite outcome set. -/

/-- Mobus (2022, 2-principles-of-systems-science.md:235): "Systems encode knowledge and receive and send information."
    Mobus (2022, 3-system-ontology.md:198): "information is the measure of uncertainty
    regarding the state of a message" (Mobus following Shannon; sentence continues in
    source).
    Encoding: outcome distribution→`q`; "measure of uncertainty"→`entropy q`.
    Not encoded: sender, receiver, message, knowledge (see `Channel`, Information.lean);
    this is the probabilistic special case of `hartley`.

    Shannon entropy of a finite outcome distribution. -/
noncomputable def entropy {Z : Type*} [Fintype Z] (q : Z → ℝ) : ℝ :=
  ∑ z, Real.negMulLog (q z)

/-! ## The entropy engine: imbalancing transfers strictly lower entropy

  This is Conant-Ashby's lemma's mechanism. Moving mass `δ` from a smaller pile
  `b` onto a larger pile `a` (making them more unequal, total fixed) strictly
  decreases `negMulLog a + negMulLog b`. Equivalently: spreading mass toward
  equality raises entropy; concentrating it lowers entropy. -/

/- PROOF TARGET: a fixed-sum transfer toward greater imbalance strictly lowers
   the two-pile entropy contribution.

   MATHEMATICAL INTENT:
   For `0 ≤ b ≤ a` and `0 < δ ≤ b`,
     negMulLog (a + δ) + negMulLog (b − δ) < negMulLog a + negMulLog b.
   `(a+δ, b−δ)` is more spread than `(a, b)` (same sum), so the strictly concave
   `negMulLog` gives a strictly smaller sum. This is the entropy fact that forces
   an optimal regulator to be deterministic.

   AVAILABLE TOOLS:
   - `Real.strictConcaveOn_negMulLog : StrictConcaveOn ℝ (Set.Ici 0) negMulLog`
   - express `a` and `b` as the two mirror convex combinations of `a+δ` and `b−δ`.

   STRATEGY:
   With weights `t = (a−b+δ)/s`, `u = δ/s`, `s = a−b+2δ > 0`:
     a = t·(a+δ) + u·(b−δ),   b = u·(a+δ) + t·(b−δ),   t + u = 1.
   Apply strict concavity twice (weights (t,u) and (u,t)) and add. -/
theorem negMulLog_transfer {a b δ : ℝ}
    (hab : b ≤ a) (hδ : 0 < δ) (hδb : δ ≤ b) :
    Real.negMulLog (a + δ) + Real.negMulLog (b - δ)
      < Real.negMulLog a + Real.negMulLog b := by
  have hs : 0 < a - b + 2 * δ := by linarith
  set s := a - b + 2 * δ with hs_def
  set t := (a - b + δ) / s with ht_def
  set u := δ / s with hu_def
  have ht : 0 < t := div_pos (by linarith) hs
  have hu : 0 < u := div_pos hδ hs
  have hsum : t + u = 1 := by
    rw [ht_def, hu_def, ← add_div]
    rw [div_eq_one_iff_eq (ne_of_gt hs), hs_def]; ring
  have hx : (a + δ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by linarith)
  have hy : (b - δ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by linarith)
  have hxy : (a + δ) ≠ (b - δ) := by intro h; apply absurd h; intro h'; linarith
  have key1 : t • (a + δ) + u • (b - δ) = a := by
    rw [ht_def, hu_def]; simp only [smul_eq_mul]; field_simp; ring
  have key2 : u • (a + δ) + t • (b - δ) = b := by
    rw [ht_def, hu_def]; simp only [smul_eq_mul]; field_simp; ring
  have happ1 := (Real.strictConcaveOn_negMulLog).2 hx hy hxy ht hu hsum
  have happ2 := (Real.strictConcaveOn_negMulLog).2 hx hy hxy hu ht (by linarith)
  rw [key1] at happ1
  rw [key2] at happ2
  have hcomb := add_lt_add happ1 happ2
  simp only [smul_eq_mul] at hcomb
  have hrw : t * Real.negMulLog (a + δ) + u * Real.negMulLog (b - δ)
      + (u * Real.negMulLog (a + δ) + t * Real.negMulLog (b - δ))
      = Real.negMulLog (a + δ) + Real.negMulLog (b - δ) := by
    linear_combination (Real.negMulLog (a + δ) + Real.negMulLog (b - δ)) * hsum
  linarith [hcomb, hrw]

/-! ## The Good Regulator theorem (determinism of optimal regulators)

  Setup: reguland distribution `pS`, outcome map `psi : R → S → Z`, regulator
  `k : S → R → ℝ` (conditional p(R|S), nonneg). The induced outcome distribution
  is `outcomeDist`. Conant-Ashby: an entropy-optimal regulator is *deterministic
  per state* — for each `s`, every positive-probability response maps to one
  outcome — from which the simplest optimal regulator is a mapping `h : S → R`. -/

variable {S R Z : Type*} [Fintype S] [Fintype R] [Fintype Z] [DecidableEq R] [DecidableEq Z]

/-- The outcome distribution induced by regulator `k` under reguland
    distribution `pS` and outcome map `psi`: `p(Z = z) = Σ_{s,r : ψ(r,s)=z} pS s · k s r`. -/
noncomputable def outcomeDist (pS : S → ℝ) (psi : R → S → Z) (k : S → R → ℝ) : Z → ℝ :=
  fun z => ∑ s, ∑ r, if psi r s = z then pS s * k s r else 0

/- DETERMINISM THEOREM — scoped target (engine above is proved; this wrapper is next).

   theorem good_regulator_deterministic
       (pS : S → ℝ) (psi : R → S → Z) (k : S → R → ℝ)
       (hpS : ∀ s, 0 ≤ pS s) (hk : ∀ s r, 0 ≤ k s r)
       (hopt : ∀ k', (∀ s r, 0 ≤ k' s r) → (∀ s, ∑ r, k' s r = ∑ r, k s r) →
                 entropy (outcomeDist pS psi k) ≤ entropy (outcomeDist pS psi k'))
       {s : S} {r₁ r₂ : R} (hs : 0 < pS s) (h1 : 0 < k s r₁) (h2 : 0 < k s r₂) :
       psi r₁ s = psi r₂ s

   PROOF STRATEGY (the bookkeeping that wraps `negMulLog_transfer`):
   By contradiction: suppose z₁ := psi r₁ s ≠ psi r₂ s =: z₂. Move δ' := k s r₂ of
   row-s mass from r₂ to r₁ (k' := Function.update k s (update (update (k s) r₂ 0)
   r₁ (k s r₁ + k s r₂))); k' is a valid regulator (nonneg, row-sum preserved).
   TRANSFER RELATION (the one real lemma): for the modified outcome distribution,
     outcomeDist k' z = outcomeDist k z + (if z = z₁ then pS s·δ' else 0)
                                        − (if z = z₂ then pS s·δ' else 0),
   proved by `Finset.sum_sub_distrib` — only the (s,r₁),(s,r₂) terms survive.
   Then entropy differs only at z₁,z₂; by `rcases le_total (outcomeDist k z₂)
   (outcomeDist k z₁)` apply `negMulLog_transfer` (with d = pS s·δ' ≤ the smaller
   pile, since each pile ≥ its own (s,·) contribution) to get
   entropy (outcomeDist k') < entropy (outcomeDist k), contradicting `hopt`.
   Corollary: pick h s ∈ support; the deterministic h has the same outcomeDist,
   so the simplest optimal regulator is the model-mapping h : S → R. -/

end Systems
