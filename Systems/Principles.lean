/-
  Systems/Principles.lean — Mobus's twelve principles, the front door.

  One re-export per principle, in Mobus's order, each restating the headline
  theorem with its full signature so this file reads as the outline of the
  result and `#print axioms` can be pointed at any line of it
  (`scripts/axiom-profile.sh` targets the originals; the names here are aliases
  that reduce to them definitionally, so the profiles agree).

  Verdicts (docs/paper/axiom-table.md, computed 2026-09-04): the twelve
  principles are four ontological primitives (#1 Systemness, #4 Dynamics,
  #6 Evolution as `EvolutionE`, #8 Governance as `HomeostatD`), two structural
  refinements of Systemness (#3 Networks = the bond graph read as a flow graph;
  #2 Hierarchy = decomposition + within>between strength, presupposing #1 by
  construction), two agential stances (#11 Understandability, #12 Improvability
  in `DirectedAgent` / `DirectedUnderModel` form; bare `Improvement` is vacuous,
  `improved_iff_moving`), and four theorems (#5 #7 #9 #10). Condition: #8 is
  independent of #6 provided evolution's criterion is external, Mobus's own
  clause; with the fitness family free every governing law is also
  environment-evolving (`evolvesByEnv_settle`). "Eight axioms" (2026-06-09 to
  2026-09-03) names the eight structures below, which remain pairwise distinct.

  Where the count is computed: Systems/Principles/Witnesses.lean (separating
  instances), Matrix.lean (within-block independence matrix, 76 declarations),
  Hierarchy.lean (`principle2_hierarchical`), NonDegenerate.lean (the sharpened
  predicates), EnvRelative.lean (`EvolutionE` / `HomeostatD` and their
  separations), over Systems/Core/JointState.lean and EnvState.lean.
  What is NOT here: the within-block matrix is decided; the cross-block cells
  are now statable through `EnvState` / `JointState` but have not been run.
  Only the listed witnesses are checked; see docs/paper/p3-reading-edition.md §9.

  Reading edition (prose + math + pointers): docs/paper/p3-reading-edition.md.
  Full findings: docs/reference/principles-formalization-companion.md.
-/
import Systems.Core
import Systems.Mobus.FlowNetwork

namespace Systems

/-! ## Axioms — the eight primitive structures

  "Axiom" here means: a `structure` whose fields no other principle's structures
  produce. It is a definition of a kind of object (what a Homeostat *is*), not an
  asserted proposition; theorems quantify over its instances, and every structure
  is inhabited by a concrete value in source (consistency). -/

/-- **#1 Systemness** (axiom, `ConcreteSystem`, Systemness.lean). A system's composition
    is organized: its bondage is non-empty, so it is not a bare aggregate. -/
theorem principle1_systemness {α : Type*} [ActsOn α] (σ : ConcreteSystem α) :
    IsOrganized σ.composition :=
  ConcreteSystem.composition_organized σ

/-- **#2 Hierarchy** (Bunge ancestry form; `ImmediateAncestor`, Level.lean). The ancestor
    relation is transitive: levels stack. NOTE (2026-09-04): this structure is a bare relation
    and asserts nothing (independence matrix); the paper's #2 is `principle2_hierarchical` in
    `Systems/Principles/Hierarchy.lean`, on Mobus Eq. 4.3 `RecursiveComponent` + Simon's
    `NearDecomposable`, which can fail. Kept here so `#print axioms` on the old showcase stays
    reproducible. -/
theorem principle2_hierarchy {α : Type*} [ImmediateAncestor α] {x y z : α}
    (hxz : Ancestor x z) (hzy : Ancestor z y) : Ancestor x y :=
  ancestor_trans hxz hzy

/-- **#3 Networks** (axiom, `FlowNetwork`, Mobus/FlowNetwork.lean). The relation a flow
    network induces has no self-loops. -/
theorem principle3_networks {α κ : Type*} (net : FlowNetwork α κ) :
    ∀ p ∈ net.toRelation, p.1 ≠ p.2 :=
  FlowNetwork.toRelation_irrefl net

/-- **#4 Dynamics** (axiom, `DynamicSystem` / `CoupledDynamicSystem`, Dynamics.lean).
    Two coupled systems are jointly at equilibrium iff the combined law fixes the pair. -/
theorem principle4_dynamics {α : Type*} [ActsOn α] {S₁ S₂ : Type*}
    {cds : CoupledDynamicSystem α S₁ S₂} {s₁ : S₁} {s₂ : S₂} :
    CoupledEquilibrium cds.law₁ cds.law₂ s₁ s₂ ↔
      IsEquilibrium cds.combinedLaw (s₁, s₂) :=
  coupled_equilibrium_iff_fixed

/-- **#6 Evolution** (axiom, `Evolution` / `Evolvable`, Evolution.lean). Blind change:
    the 3-cycle is evolvable yet admits no directed agent, so #6 does not yield #12. -/
theorem principle6_evolution :
    Evolvable (Fin 3) ∧
      (∀ (M : Type) (a : DirectedAgent (Fin 3) M),
        (∀ x : Fin 3, a.understanding.systemDyn x = x + 1) → False) :=
  evolvable_but_not_improvable

/-- **#8 Governance** (axiom, `Homeostat`, Governance.lean). Under the neutrality
    conditions, the set-point is an equilibrium of the feedback law. -/
theorem principle8_governance {S O : Type*} (h : Homeostat S O) (s : S)
    (h_at : h.atTarget s)
    (h_error_zero : ∀ o, h.error o o = h.error h.setPoint h.setPoint)
    (h_correct_neutral : ∀ s', h.correct (h.error h.setPoint h.setPoint) s' = s') :
    IsEquilibrium h.feedbackLaw s :=
  Homeostat.target_is_equilibrium h s h_at h_error_zero h_correct_neutral

/-- **#11 Understandability** (axiom, `Understanding`, Understanding.lean). An
    understanding whose abstraction is the identity does not exist: understanding must
    compress. -/
theorem principle11_understandability {S : Type*} (u : Understanding S S)
    (h : u.abstract = id) : False :=
  no_trivial_understanding u h

/-- **#12 Improvability** (axiom, `Improvement` / `DirectedAgent`, Improvability.lean).
    The goal is not a function of the dynamics: one dynamics, two improvements, two goals. -/
theorem principle12_improvability :
    ∃ (dyn : Bool → Bool) (imp₁ imp₂ : Improvement Bool),
      imp₁.dyn = dyn ∧ imp₂.dyn = dyn ∧ imp₁.goal ≠ imp₂.goal :=
  goal_is_external

/-! ## Theorems — the four derived notions

  Each is *definable* from the axioms' structures (no new primitive: #5 is a def
  over `ActsOn`, #9 over #4's dynamics, #10 is #9 with `R = S`, #7 is stated
  through #9's model). Their content is the theorem proved about the derived
  notion, not a new commitment. -/

/-- **#5 Complexity** (theorem from #1 #2 #3, Complexity.lean). Kind-diversity is an
    equivalence derived from the acts-on relation alone; the first reduction, 12 → ≤ 11. -/
theorem principle5_complexity {α : Type*} [ActsOn α] :
    Equivalence (@SameKind α _) :=
  sameKind_equivalence

/-- **#7 Information** (theorem, layered, Information.lean). Shannon entropy is bounded
    by Hartley nonspecificity: `log |Z|`, with equality at the uniform distribution. -/
theorem principle7_information {Z : Type*} [Fintype Z] [Nonempty Z]
    (p : Z → ℝ) (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) :
    entropy p ≤ Real.log (Fintype.card Z) :=
  entropy_le_log_card p hp hsum

/-- **#9 Internal Models** (theorem from #4, InternalModel.lean). A one-step-correct
    model is correct at every horizon; a fast model with `lead` runs `n * lead` ahead. -/
theorem principle9_internal_models {R S : Type*} (am : AnticipatoryModel R S)
    (n : ℕ) (r : R) :
    am.model (am.internalDyn^[n] r) = am.systemDyn^[n * am.lead] (am.model r) :=
  AnticipatoryModel.tracks am n r

/-- **#10 Self-Models** (theorem, the diagonal of #9, SelfModel.lean). An accurate fast
    self-model forces its own orbit into periodicity. -/
theorem principle10_self_models {S : Type*} (fsm : FastSelfModel S) {s : S} {n : ℕ}
    (h1 : fsm.accurate s) (h2 : fsm.accurate (fsm.dyn^[n] s)) :
    fsm.dyn^[n * (fsm.lead - 1)] (fsm.dyn^[n] s) = fsm.dyn^[n] s :=
  FastSelfModel.accurate_forces_periodic fsm h1 h2

/-! ## Witnesses — separating instances

  A separating instance is a concrete value that satisfies one principle's
  structure and provably cannot satisfy another's; it shows the second is not a
  consequence of the first. The witnesses below are the original four; the full
  within-block matrix (every ordered pair separated by a witness or realized by a
  derivation) is Systems/Principles/Matrix.lean, and the environment-relative
  separations of #6 from #8 are Systems/Principles/EnvRelative.lean. Cross-block
  pairs remain unrun; no theorem here asserts them. -/

/-- **#9 ⇏ #11, minimal.** A one-state system has a model and no understanding. -/
theorem witness_modeling_not_understanding :
    (∃ _ : InternalModel Unit Unit, True) ∧ (∀ M, Understanding Unit M → False) :=
  modeling_does_not_imply_understanding

/-- **#9 ⇏ #11, dynamical.** The 3-cycle has a model and no understanding: the
    obstruction is incompressible dynamics, not cardinality. -/
theorem witness_cyclic3_modeling_not_understanding :
    (∃ _ : InternalModel (Fin 3) (Fin 3), True) ∧
      (∀ (M : Type) (u : Understanding (Fin 3) M),
        (∀ x : Fin 3, u.systemDyn x = x + 1) → False) :=
  cyclic3_modeling_not_understanding

/-- **#6 ⇏ #12.** The 3-cycle is evolvable and not improvable: #6 holds, #12 fails
    (same statement as `principle6_evolution`; listed here as the witness). The converse
    direction, #12 ⇏ #6, has no witness in source. -/
theorem witness_evolvable_not_improvable :
    Evolvable (Fin 3) ∧
      (∀ (M : Type) (a : DirectedAgent (Fin 3) M),
        (∀ x : Fin 3, a.understanding.systemDyn x = x + 1) → False) :=
  evolvable_but_not_improvable

/-- **#8 realizes #12.** A homeostat at target yields an improvement (the governance
    engine is the realized form of directed intervention). -/
noncomputable example {S O : Type*} (h : Homeostat S O) (s : S) (dyn : S → S)
    (h_at : h.atTarget s)
    (h_error_zero : ∀ o, h.error o o = h.error h.setPoint h.setPoint)
    (h_correct_neutral : ∀ s', h.correct (h.error h.setPoint h.setPoint) s' = s')
    (h_genuine : ¬ IsEquilibrium dyn s) : Improvement S :=
  Homeostat.toImprovement h s dyn h_at h_error_zero h_correct_neutral h_genuine

end Systems
