/-
  Systems/Core/Evolution.lean
  Principle 6: Evolution — "Systems evolve to accommodate long-term changes in their
  environments." The blind pillar — counterpart to the agential layer (#11/#12).

  Mobus labels #12 (Improvability) "a corollary of #6." We have already shown #12 is an
  independent agential axiom (Improvability.lean); here we formalize #6 itself and show it
  is the independent *blind* axiom. They share one ontogenic skeleton (variation → selection
  → retention) but differ in the selecting agent: #6's criterion is environmental, #12's goal
  is mental. Neither reduces to the other.

  SOURCE GROUNDING (Mobus & Kalton 2015, Principles of Systems Science, Ch. 10).
  - §10.2.2 "Evolution as a Kind of Algorithm" gives evolution as an explicit iterated
    variation → selection → retention procedure whose net effect is "the varieties having
    the greatest fitness will tend to dominate the population" over generations. We formalize
    the deterministic, fitness-monotone core of that algorithm.
  - §10.2.1.4 "Fit and Fitness": fitness is "inherently relational… has no meaning without
    considering a system's environment." So fitness is a PREORDER — an environmental
    criterion — not a numeric objective.
  - The decisive line: "what is selected for is always a matter of fit with some sort of
    criterion … the criterion is NOT resident in some mind but in the conditions imposed by …
    the surrounding system." Evolution's selection is environmental and BLIND. This is exactly
    what distinguishes it from #12, whose goal lives in an agent's mind.

  THE FORMALIZATION.
  An `Evolution S` over a fitness preorder `[Preorder S]` is a generational `step : S → S`
  whose only law is `selects : ∀ s, s ≤ step s` — each generation is at least as fit. There
  is deliberately NO model, goal, or understanding field: that blindness is the whole point,
  and it is what makes #6 applicable to ANY system, including systems #12 cannot touch.

  WHAT IS PROVED.
  - `Evolution.adapts`: fitness is monotonically non-decreasing across ALL generations
    (one-step `selects` lifts to all horizons — the #6 analogue of #11's `tracks` / #12's
    `persists`).
  - `Evolvable`: the CAES capacity — a system that CAN strictly improve (is not everywhere at
    a fitness ceiling). Distinct from the act of evolving (Mobus's evolvability-as-property).
  - `Evolution.IsAdapted`: a fitness peak — a state selection no longer improves; the fixed
    point the monotone climb approaches (light adaptation-vs-evolution).
  - `evolvable_but_not_improvable` (the capstone, #6 ⇏ #12): the prime-cyclic 3-cycle is
    evolvable, yet (by Improvability.lean's `cyclic3_no_directed_improvement`) admits no
    directed agent. **A prime-cyclic system can be blindly evolved but not deliberately
    improved** — blind selection needs no mind; directed engineering does. This completes the
    blind-vs-directed trichotomy and the 12 principles.

  Bunge substrate: `Selection.lean` formalizes the set-level static selective action
  (population → adapted, with `compose_adapted_sub : A_{EE'} ⊆ A_E` — iterated selection
  narrows the survivors). Evolution adds the fitness preorder (the *why*) and the temporal
  monotonicity (the *direction*) that the set-level account abstracts away.

  Deferred (research-level, not gaps): explicit populations/replicators and mutation operators;
  stochastic / expected-fitness selection and the Price equation (needs probability — same
  discipline as #7's Shannon deferral); fitness landscapes (Kauffman NK); the thermodynamic
  free-energy framing (Mobus 2022 Ch. 2, evolving/steady/decaying); genetic drift / neutral
  evolution; multi-level selection; the full adaptation-vs-evolution timescale treatment. The
  core captures selection/adaptation (the directional climb), not the full variation machinery.
-/

import Systems.Core.Improvability
import Systems.Core.Selection

namespace Systems

/-! ## Evolution as blind, fitness-monotone selection -/

/-- Mobus (2022, 2-principles-of-systems-science.md:234): "Systems evolve to accommodate long-term changes in their
    environments."
    Mobus (2022, 2-principles-of-systems-science.md:346–347): "All systems can be in one of three situations. They can be
    evolving toward higher organization, maintaining a steady-state dynamic, or decaying."
    (footnote marker omitted)
    Mobus & Kalton (2015, mobus-kalton-2015/10-auto-organization-and-emergence.md:506–508):
    "what is selected for is always a matter of fit with some sort of criterion." ... "the
    criterion is not resident in some mind but in the conditions imposed by the nature,
    shape, and functioning of the surrounding system."
    Encoding: "evolve"→`step` (one generation); "fit with some sort of criterion ... imposed by
    ... the surrounding system"→the fitness preorder `≤` on `S`; selection→`selects`
    (`s ≤ step s`); "evolving toward higher organization"→`Evolvable` (strict improvement
    exists); "steady-state"→`IsAdapted` (fixed point).
    Not encoded: "long-term changes in their environments" (the preorder is fixed — the
    environment does not change); "decaying" (fitness is non-decreasing by law); variation
    and retention as separate operators; populations; the energy-flow basis Mobus gives for
    the principle.

    An `Evolution` over a system whose configurations are ordered by environmental fitness
    (`[Preorder S]`, with `a ≤ b` meaning "b is at least as fit as a"): a generational
    `step : S → S` that is fitness-non-decreasing (`selects`). The net variation+selection
    operator of M&K's algorithm. There is no model/goal/understanding — selection is blind,
    its criterion environmental. -/
structure Evolution (S : Type*) [Preorder S] where
  /-- One generation: the net effect of variation followed by environmental selection. -/
  step : S → S
  /-- Selection is fitness-non-decreasing: a generation is at least as fit as its parent.
      The criterion is the environment's order, not a goal in any mind. -/
  selects : ∀ s, s ≤ step s

/-- Fitness is monotonically non-decreasing across every horizon of generations: a system
    under selection never gets less fit. One-step `selects` lifts to all generations — the
    #6 counterpart of #11's `tracks` and #12's `persists`. -/
theorem Evolution.adapts {S : Type*} [Preorder S] (e : Evolution S) (n : ℕ) (s : S) :
    s ≤ e.step^[n] s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact le_trans ih (e.selects _)

/-- A state is **adapted** when selection no longer improves it — a fitness peak, a fixed
    point of the generational step. Adaptation is the rest state the monotone climb approaches;
    evolution is the climb. -/
def Evolution.IsAdapted {S : Type*} [Preorder S] (e : Evolution S) (s : S) : Prop :=
  IsEquilibrium e.step s

/-- **Evolvability** (the CAES property): a system *can* evolve — there is an evolutionary
    process and a state that strictly improves under it. This is a capacity, distinct from the
    act of evolving; a system everywhere at a fitness ceiling is not evolvable. -/
def Evolvable (S : Type*) [Preorder S] : Prop :=
  ∃ (e : Evolution S) (s : S), s < e.step s

/-! ## Non-vacuity — a system that genuinely evolves

  `Fin 3` under its linear order stands in for an environmental fitness criterion; the step
  climbs toward the fittest state. -/

/-- A fitness-climbing generational step on three configurations: each generation moves to a
    strictly fitter state until the peak is reached. -/
def fin3climb : Fin 3 → Fin 3 := fun x => if x = 2 then 2 else x + 1

/-- The three-state system is evolving: the climb is fitness-non-decreasing everywhere. -/
def fin3evolution : Evolution (Fin 3) where
  step := fin3climb
  selects := by decide

/-! ## The capstone: blind selection succeeds where directed design cannot

  Evolution needs no model, goal, or understanding — only an environmental fitness order — so
  it runs on ANY system. In particular it runs on the prime-cyclic 3-cycle that #12 cannot
  improve (it has a model but no understanding, `Improvability.cyclic3_no_directed_improvement`).
  The un-engineerable is still evolvable. -/

/-- **#6 ⇏ #12.** The three-state system is evolvable, yet the prime-cyclic dynamics `x ↦ x+1`
    on it admit no directed agent. A prime-cyclic system **can be blindly evolved but not
    deliberately improved**: blind selection needs no mind, directed engineering does. This is
    the formal seam between Evolution (#6) and Improvability (#12), completing the blind-vs-
    directed trichotomy — and, with it, all 12 principles. -/
theorem evolvable_but_not_improvable :
    Evolvable (Fin 3) ∧
      (∀ (M : Type) (a : DirectedAgent (Fin 3) M),
        (∀ x : Fin 3, a.understanding.systemDyn x = x + 1) → False) :=
  ⟨⟨fin3evolution, 0, by decide⟩, fun _ a h => cyclic3_no_directed_improvement a h⟩

end Systems
