/-
  Systems/Joslyn/Control.lean
  Joslyn's Control₁/Control₂ hierarchy + Prop 29 tractable core
  (categorification roadmap Phase 4.2)

  Joslyn, "Semantic Control Systems" (World Futures 45:87-123, 1995), §3.

  Def 25 (Control₁): a metasystem CS = ⟨C, O⟩ is a control₁ system if the
  actions of the controller C result in a constraint₂ (a genuine reduction
  of variety) on the freedom of O. Passive: the ball rolls to the valley
  floor. Guards from the text: dissociation excluded (§3.3.1 — C must
  genuinely act) and overconstraint excluded (§3.3.2 — an already-fully-
  constrained O has no variety left to constrain).

  Def 28 (Control₂): a control₁ system where the variation in the
  constraint₁ on O, induced by C's variation, is ITSELF constrained₂ —
  second-order stability at a hierarchically distinct level. Marken's
  Def 27 is the descriptive face: "a physical variable that remains stable
  in the face of factors that should produce variability." "Constrained₂"
  means REDUCED second-order variety, not eliminated — hence the
  `maintained` field (a surviving region), not full envelope-invariance.

  Prop 29: given control₂ CS = ⟨C, O⟩, O is itself a control₁ system
  O = ⟨O_E, O_I⟩ — the efferent component's varying constraint on the
  controlled variables CANCELS C's variation ("the variation of C and the
  variation of O_E cancel, yielding the overall constraint₁ of O_I
  constant"). Joslyn derives this from Mesarovic 1964 (p. 14: systems of
  dimension ≥ 3 do not decompose into 2-fold input/output systems — they
  require internal state).

  TRACTABLE CORE vs DEFERRED: `Control₂Realized` carries Prop 29's
  decomposition as data, and the coherence theorems below prove the
  realization IS control₂ (outer) and contains control₁ (inner), with the
  cancellation explicit. The EXISTENCE direction — every control₂ system
  admits such a decomposition — is Prop 29's Mesarovic-dependent content
  and is DEFERRED until Mesarovic 1964 is formalized (the same posture as
  Lawvere for the faithful self-model, #10).

  MARKEN-FACE CHOICE: the outer control₂ extracted from a realization
  lands on the controlled variables I (Marken's "controlled event" IS
  O_I), not on the product E × I — the effector's whole role is to VARY,
  so a product-shaped stable region misrepresents the compensation.
-/

import Mathlib.Data.Set.Lattice
import Systems.Joslyn.JoslynSystem
import Systems.Core.Governance

namespace Systems

/-! ## Control₁ (Def 25) -/

/-- Joslyn's control₁ (1995, Def 25): each controller state induces a
    constraint₁ — an envelope — on the object's states, and the constraint
    is genuine: nonempty (overconstraint guard, §3.3.2) and a proper
    reduction of variety (dissociation guard, §3.3.1). -/
structure Control₁ (C O : Type*) where
  /-- The constraint₁ that each controller state places on O. -/
  envelope : C → Set O
  /-- Overconstraint guard (§3.3.2): the envelope never collapses to ∅. -/
  envelope_nonempty : ∀ c, (envelope c).Nonempty
  /-- Genuine variety reduction (Def 24/25; dissociation guard §3.3.1). -/
  constrains : ∀ c, envelope c ≠ Set.univ

/-! ## Control₂ (Def 28) -/

/-- Joslyn's control₂ (1995, Def 28): a control₁ system where the
    second-order variation — the variation of the envelope induced by C's
    variation — is itself constrained₂: a nonempty region `stable` (O*)
    survives inside EVERY induced envelope. Marken's Def 27 is the
    descriptive face: the variable stays in O* despite factors (C's
    variation) that should move it. -/
structure Control₂ (C O : Type*) extends Control₁ C O where
  /-- O*: the maintained region. -/
  stable : Set O
  /-- O* is a genuine region. -/
  stable_nonempty : stable.Nonempty
  /-- Def 28: O* survives C's variation — second-order constraint₂. -/
  maintained : ∀ c, stable ⊆ envelope c

/-! ## Prop 29's decomposition, as a realization structure

  The internal anatomy Prop 29 asserts: C disturbs the effector (h), the
  effector constrains the controlled variables (g), and the composite
  constraint on the controlled variables is invariant — the cancellation. -/

/-- A realized control₂ system (Prop 29's decomposition as data):
    `CS = ⟨C, O = ⟨O_E, O_I⟩⟩`. `disturb` is Joslyn's h (the global
    environment's variation hitting the effector), `effect` is g (the
    effector's constraint₁ on the controlled variables), and `compensates`
    is the cancellation: however C varies, the composite constraint on the
    controlled variables is the SAME stable region — "the variation of C
    and the variation of O_E cancel." The existence direction (every
    control₂ admits such a realization) is deferred on Mesarovic 1964. -/
structure Control₂Realized (C E I : Type*) where
  /-- h: the envelope C's variation imposes on the effector. -/
  disturb : C → Set E
  /-- g: the constraint each effector state places on the controlled
      variables. -/
  effect : E → Set I
  /-- The disturbance envelope is never empty. -/
  disturb_nonempty : ∀ c, (disturb c).Nonempty
  /-- The effector's constraint is never empty. -/
  effect_nonempty : ∀ e, (effect e).Nonempty
  /-- The effector genuinely constrains the controlled variables. -/
  effect_constrains : ∀ e, effect e ≠ Set.univ
  /-- O*_I: the maintained region of the controlled variables. -/
  stableI : Set I
  /-- The maintained region is a genuine constraint. -/
  stableI_ne_univ : stableI ≠ Set.univ
  /-- The cancellation (Prop 29): the composite constraint on the
      controlled variables is invariant under C's variation. -/
  compensates : ∀ c, (⋃ e ∈ disturb c, effect e) = stableI

namespace Control₂Realized

variable {C E I : Type*} (R : Control₂Realized C E I)

/-- The maintained region is nonempty: any controller state's disturbance
    admits an effector state, whose effect is nonempty and lands inside
    the (invariant) composite constraint. -/
theorem stableI_nonempty [Nonempty C] : R.stableI.Nonempty := by
  obtain ⟨c⟩ := ‹Nonempty C›
  obtain ⟨e, he⟩ := R.disturb_nonempty c
  obtain ⟨i, hi⟩ := R.effect_nonempty e
  rw [← R.compensates c]
  exact ⟨i, Set.mem_biUnion he hi⟩

/-- Prop 29's cancellation, stated as invariance: the composite constraint
    the effector transmits to the controlled variables does not depend on
    the controller's state — "the variation of C and the variation of O_E
    cancel." -/
theorem cancellation (c c' : C) :
    (⋃ e ∈ R.disturb c, R.effect e) = ⋃ e ∈ R.disturb c', R.effect e := by
  rw [R.compensates c, R.compensates c']

/-- Prop 29 coherence, outer face: a realized control₂ system IS a control₂
    system over the controlled variables (the Marken face — his "controlled
    event" is O_I; the product E × I misrepresents the compensation since
    the effector's role is to vary). The envelope is the composite
    constraint; the maintained region is O*_I. -/
def toControl₂ [Nonempty C] : Control₂ C I where
  envelope := fun c => ⋃ e ∈ R.disturb c, R.effect e
  envelope_nonempty := fun c => by
    obtain ⟨e, he⟩ := R.disturb_nonempty c
    obtain ⟨i, hi⟩ := R.effect_nonempty e
    exact ⟨i, Set.mem_biUnion he hi⟩
  constrains := fun c => by
    rw [R.compensates c]
    exact R.stableI_ne_univ
  stable := R.stableI
  stable_nonempty := R.stableI_nonempty
  -- why: (compensates c).ge routes through the classical Set order instance;
  -- direct membership transport keeps the construction axiom-free
  maintained := fun c => fun _ hi => (R.compensates c).symm ▸ hi

/-- Prop 29's inner claim: the realized object is ITSELF a control₁ system
    O = ⟨O_E, O_I⟩ — the effector controls₁ the controlled variables. -/
def toControl₁ : Control₁ E I where
  envelope := R.effect
  envelope_nonempty := R.effect_nonempty
  constrains := R.effect_constrains

end Control₂Realized

/-! ## The Governance bridge (#8)

  "The Joslyn formalization IS the Governance formalization" (roadmap):
  a homeostat that genuinely regulates realizes control₂. -/

/-- A singleton is never the whole of a nontrivial type — constructive
    replacement for Mathlib's `Set.singleton_ne_univ`, which pulls
    `Classical.choice`; this proof pulls no axioms at all. -/
theorem singleton_ne_univ' {α : Type*} [Nontrivial α] (a : α) :
    ({a} : Set α) ≠ Set.univ := by
  intro heq
  obtain ⟨x, y, hxy⟩ := ‹Nontrivial α›
  have hx : x ∈ ({a} : Set α) := heq ▸ Set.mem_univ x
  have hy : y ∈ ({a} : Set α) := heq ▸ Set.mem_univ y
  exact hxy (hx.trans hy.symm)

/-- Every PERFECT homeostat — one whose feedback law reaches the set point
    in one tick (`hreach`) — realizes Joslyn's control₂: disturbed states
    force the compensating action (h), the sensor reads out the controlled
    variable (g), and the composite readout is pinned to the set point —
    the cancellation. This machine-checks the roadmap's claim that the
    Joslyn formalization IS the Governance formalization, for perfect
    regulators; the asymptotic version (set point reached in the limit)
    needs dynamics and is deferred. -/
def Homeostat.toControl₂Realized {S O : Type*} [Nontrivial O]
    (h : Homeostat S O)
    (hreach : ∀ s, h.sensor (h.feedbackLaw s) = h.setPoint) :
    Control₂Realized S S O where
  disturb := fun s => {h.feedbackLaw s}
  effect := fun s' => {h.sensor s'}
  disturb_nonempty := fun s => Set.singleton_nonempty _
  effect_nonempty := fun s' => Set.singleton_nonempty _
  effect_constrains := fun s' => singleton_ne_univ' _
  stableI := {h.setPoint}
  stableI_ne_univ := singleton_ne_univ' _
  -- why: simp / Set.biUnion_singleton route through classical lemmas; the
  -- elementary two-inclusion proof keeps the bridge choice-free
  compensates := fun s => by
    apply Set.Subset.antisymm
    · intro o ho
      obtain ⟨s', hs', ho'⟩ := Set.mem_iUnion₂.mp ho
      rw [Set.mem_singleton_iff] at hs' ho' ⊢
      rw [ho', hs', hreach s]
    · intro o ho
      rw [Set.mem_singleton_iff] at ho
      refine Set.mem_biUnion (Set.mem_singleton _) ?_
      rw [Set.mem_singleton_iff, ho, hreach s]

end Systems
