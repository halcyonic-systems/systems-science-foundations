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
    its criterion environmental.

    **This is the frozen-environment case of `EvolutionE`** (below): one fitness order,
    an environment that never moves. `Evolution.freeze` is the embedding. -/
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

/-! ## Environment-relative evolution (decision B, 2026-09-04)

  `Evolution` fixes one preorder on `S`; its docstring's `Not encoded:` line is
  "long-term changes in their environments" (Mobus 2022, principle #6 verbatim). M&K
  §10.2.1.4 say fitness "has no meaning without considering a system's environment", so
  the fitness order is indexed BY the environment, and #6 says the environment moves.
  `EvolutionE` carries both: a family `fit : E → Preorder S` (the rendering
  `EvolvesByEnv` in Principles/NonDegenerate.lean already uses on the tied law), a step on
  the product `S × E`, and selection relative to the CURRENT environment. The carrier
  `S × E` is `JointStateE` (Core/EnvState.lean) when the CES index is in play. -/

/-- Mobus (2022, 2-principles-of-systems-science.md:234): "Systems evolve to accommodate
    long-term changes in their environments."
    Mobus & Kalton (2015, 10-auto-organization-and-emergence.md, §10.2.1.4): fitness "is
    inherently relational ... has no meaning without considering a system's environment."
    Encoding: "their environments"→the coordinate `E`; "fit ... considering a system's
    environment"→`fit : E → Preorder S`, one order per environment; "evolve"→`step` on
    `S × E`; selection→`selects`, relative to the environment the generation was selected
    IN; "long-term changes in their environments"→`EnvMoves` (the environment coordinate
    changes somewhere) — the line `Evolution` could not encode.
    Not encoded: which of the two coordinates drives the other (the step is one joint map);
    "long-term" as a timescale separation; decay; populations and variation operators.

    An environment-relative evolution: a fitness order for each environment, and a joint
    step that never lowers fitness relative to the current environment. -/
structure EvolutionE (S E : Type*) where
  /-- The fitness order in environment `e`: `a ≤ b` means "b is at least as fit as a" in `e`. -/
  fit : E → Preorder S
  /-- One generation of the system AND its environment. -/
  step : S × E → S × E
  /-- Selection relative to the current environment: the next system state is at least as
      fit, in the order of the environment it was selected in. -/
  selects : ∀ s e, @LE.le S (fit e).toLE s (step (s, e)).1

/-- The environment moves somewhere: the joint step changes the environment coordinate at
    some point. This is the "long-term changes in their environments" clause. -/
def EvolutionE.EnvMoves {S E : Type*} (ev : EvolutionE S E) : Prop :=
  ∃ s e, (ev.step (s, e)).2 ≠ e

/-- The system strictly climbs somewhere, relative to the current environment. -/
def EvolutionE.Climbs {S E : Type*} (ev : EvolutionE S E) : Prop :=
  ∃ s e, @LT.lt S (ev.fit e).toLT s (ev.step (s, e)).1

/-- **Environment-relative evolvability**: some environment-relative evolution on the
    carrier both climbs somewhere and moves its environment somewhere. `Evolvable` asked
    only for the climb; #6's "changes in their environments" is the second clause.
    A frozen environment (`E := Unit`) is never `EvolvableE` — see `not_evolvableE_unit`. -/
def EvolvableE (S E : Type*) : Prop :=
  ∃ ev : EvolutionE S E, ev.Climbs ∧ ev.EnvMoves

/-! ### The frozen case: `Evolution` embeds as `EvolutionE` over `Unit` -/

/-- Freeze the environment: an `Evolution S` over the ambient order is an `EvolutionE S Unit`
    with the constant fitness family and an environment coordinate that never moves. -/
def Evolution.freeze {S : Type*} [inst : Preorder S] (e : Evolution S) : EvolutionE S Unit where
  fit := fun _ => inst
  step := fun p => (e.step p.1, ())
  selects := fun s _ => e.selects s

/-- Thaw: an `EvolutionE S Unit` whose fitness family is the ambient order is an
    `Evolution S` (drop the environment coordinate). -/
def EvolutionE.thaw {S : Type*} [inst : Preorder S] (ev : EvolutionE S Unit)
    (hfit : ev.fit = fun _ => inst) : Evolution S where
  step := fun s => (ev.step (s, ())).1
  selects := fun s => by
    have h := ev.selects s ()
    rw [hfit] at h
    exact h

/-- The frozen environment never moves. `#print axioms`: none. -/
theorem Evolution.freeze_not_envMoves {S : Type*} [Preorder S] (e : Evolution S) :
    ¬ e.freeze.EnvMoves :=
  fun ⟨_, _, h⟩ => h rfl

/-- Over `Unit` nothing is `EvolvableE`: there is no second environment to move to. The
    old `Evolvable` therefore does NOT embed into `EvolvableE` verbatim — it embeds into
    the climb clause alone (`evolvable_iff_frozen_climbs`). `#print axioms`: none. -/
theorem not_evolvableE_unit (S : Type*) : ¬ EvolvableE S Unit :=
  fun ⟨_, _, _, _, h⟩ => h rfl

/-- **`Evolution` is the frozen case, on the climb clause.** Under the ambient order,
    `Evolvable S` holds iff some `EvolutionE S Unit` with the constant fitness family
    climbs. The environment-moves clause is exactly what the frozen case lacks.
    `#print axioms`: none. -/
theorem evolvable_iff_frozen_climbs (S : Type*) [inst : Preorder S] :
    Evolvable S ↔ ∃ ev : EvolutionE S Unit, ev.fit = (fun _ => inst) ∧ ev.Climbs := by
  constructor
  · rintro ⟨e, s, hs⟩
    exact ⟨e.freeze, rfl, s, (), hs⟩
  · rintro ⟨ev, hfit, s, _, hs⟩
    refine ⟨ev.thaw hfit, s, ?_⟩
    change @LT.lt S inst.toLT s (ev.step (s, ())).1
    rw [hfit] at hs
    exact hs

/-- Non-vacuity of the frozen embedding: the three-state climb, frozen. -/
def fin3evolutionE : EvolutionE (Fin 3) Unit := fin3evolution.freeze

/-! ### `EvolvableE` at the carrier level is still a cardinality fact

  `evolvable_iff_exists_lt'` (Principles/Matrix.lean) showed `Evolvable S` is a property of
  the order alone. With the fitness family free, `EvolvableE S E` is a property of the two
  carriers alone: two distinct system states and two distinct environments suffice. The
  content of environment-relative evolution lives in the TIED predicate `EvolvesByEnv g`
  (Principles/NonDegenerate.lean), which fixes the law; `Principles/EnvRelative.lean` ties
  `EvolutionE` to it and runs the separations there. -/

/-- Two system states and two environments make any carrier `EvolvableE`: order `s < t` in
    every environment, and step every point to `(t, e')` for the other environment. Recorded
    so that nobody reads `EvolvableE S E` as a property of a law. `#print axioms`: propext,
    Classical.choice, Quot.sound. -/
theorem evolvableE_of_pairs {S E : Type*} (hS : ∃ s t : S, s ≠ t) (hE : ∃ e e' : E, e ≠ e') :
    EvolvableE S E := by
  classical
  obtain ⟨s, t, hst⟩ := hS
  obtain ⟨e, e', hee⟩ := hE
  -- "t is fittest": `a ≤ b` iff `a = t → b = t`.
  let top : Preorder S :=
    { le := fun a b => a = t → b = t
      lt := fun a b => (a = t → b = t) ∧ ¬ (b = t → a = t)
      le_refl := fun _ h => h
      le_trans := fun _ _ _ h₁ h₂ h => h₂ (h₁ h)
      lt_iff_le_not_ge := fun _ _ => Iff.rfl }
  refine ⟨⟨fun _ => top, fun p => (t, if p.2 = e then e' else e), fun _ _ _ => rfl⟩,
    ⟨s, e, ⟨fun h => absurd h hst, fun h => hst (h rfl)⟩⟩, ⟨s, e, ?_⟩⟩
  simpa using Ne.symm hee

end Systems
