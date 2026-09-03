/-
  Systems/Principles/Witnesses.lean — separating instances for the dependency DAG
  (docs/paper/dependency-dag.mmd), Lane A of the P3 paper: "the safe claim".

  DEFINITION. "A ⇏ B" is witnessed by a concrete carrier with an instance of A's
  structure and a proof that no instance of B's structure exists on that carrier
  — the shape of `evolvable_but_not_improvable`. When B's structure is inhabited
  on EVERY carrier the pair is NOT SEPARABLE in this sense; those cases are proved
  as constructions (a def that builds B on an arbitrary carrier) or recorded in a
  comment, never left silent.

  Carriers. Components (#1 `ConcreteSystem`, #2 `ImmediateAncestor`, #3
  `FlowNetwork`) and state spaces (#4 `DynamicSystem`/law, #6 `Evolvable`, #8
  `Homeostat`, #11 `Understanding`, #12 `Improvement`/`DirectedAgent`). A witness
  is attempted only when both ends sit on the same carrier or the DAG arrow's own
  Lean home supplies the bridge.

  What this file adds beyond `Systems/Principles.lean`:
    §A  `Evolvable` is a property of the fitness order alone (`evolvable_iff_exists_lt`);
        #12 ⇏ #6 (`improvable_but_not_evolvable`), the converse the ledger listed as open.
    §B  The existing #6 ⇏ #12 witness is dynamics-specific: the evolved step and the
        improved dynamics are different maps (`cyclic3_not_evolution_step`,
        `fin3_directed_agent_exists`).
    §C  Two-state carriers admit no understanding (`no_understanding_of_le_two`), giving
        carrier-level #6 ⇏ #11, #8 ⇏ #11, #12 ⇏ #11 and the DirectedAgent form of #6 ⇏ #12.
    §D  #11 ⇏ #12 (`understandable_not_improvable`): a system at rest is understood and
        cannot be improved.
    §E  The dashed 9 → 11 arrow's forgetful direction as a theorem
        (`Understanding.toInternalModel`).
    §F  #4 ⇏ #8: NOT SEPARABLE as structures; the weak true thing
        (`setPoint_not_determined_by_law`).
    §G  Non-separability constructions for 1 → 4, 8 → 12, 9 → 8 and the remaining arrows.
    §H  #5's import list, stated exactly.

  Every theorem's `#print axioms` profile is recorded in its docstring.
-/
import Systems.Principles

namespace Systems

/-! ## §A Evolvability is a property of the fitness order

  `Evolvable S := ∃ (e : Evolution S) (s : S), s < e.step s`. The `Evolution` data is
  not load-bearing: for any `s ≤ t` the step that sends `s` to `t` and fixes everything
  else is fitness-non-decreasing, so `Evolvable S` holds exactly when the preorder has a
  strict pair. Consequence: no dynamics on a carrier can make it evolvable or not; only
  the environment's order can. This is honest to Mobus (the criterion is environmental,
  §10.2.1.4) and it means every #12 ⇏ #6 witness must use a flat fitness order — under
  any order with a strict pair, every improvable carrier is also evolvable. -/

open Classical in
/-- The jump evolution: send `s` to a fitter `t`, fix every other state. -/
noncomputable def Evolution.jump {S : Type*} [Preorder S] {s t : S} (h : s ≤ t) :
    Evolution S where
  step := fun x => if x = s then t else x
  selects := by
    intro x
    split_ifs with hx
    · subst hx; exact h
    · exact le_rfl

/-- **`Evolvable` is near-vacuous.** A carrier is evolvable iff its fitness preorder has
    a strict pair. The generational step contributes nothing beyond the order.
    Profile: `propext`, `Classical.choice`, `Quot.sound` (the jump uses classical
    decidability of equality). -/
theorem evolvable_iff_exists_lt {S : Type*} [Preorder S] :
    Evolvable S ↔ ∃ s t : S, s < t := by
  constructor
  · rintro ⟨e, s, hs⟩
    exact ⟨s, e.step s, hs⟩
  · rintro ⟨s, t, hst⟩
    refine ⟨Evolution.jump hst.le, s, ?_⟩
    simpa [Evolution.jump] using hst

/-- A carrier under the flat fitness order: no state is fitter than any other. The
    environment ranks nothing. -/
def Flat (α : Type*) := α

instance {α : Type*} : Preorder (Flat α) where
  le a b := a = b
  le_refl _ := rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂

/-- Under a flat fitness order nothing can evolve, whatever its dynamics.
    Profile: `propext`, `Classical.choice`, `Quot.sound` (via `evolvable_iff_exists_lt`). -/
theorem flat_not_evolvable {α : Type*} : ¬ Evolvable (Flat α) := by
  rw [evolvable_iff_exists_lt]
  rintro ⟨s, t, hst⟩
  exact hst.ne (hst.le : s = t)

/-- **#12 ⇏ #6.** `Bool` under the toggle admits an improvement toward `true`
    (`boolImprovement true`), yet under a flat fitness order it is not evolvable. The
    converse of `evolvable_but_not_improvable`; the ledger (§9) listed it as open.
    Profile: `propext`, `Classical.choice`, `Quot.sound`. -/
theorem improvable_but_not_evolvable :
    (∃ _ : Improvement (Flat Bool), True) ∧ ¬ Evolvable (Flat Bool) :=
  ⟨⟨boolImprovement true, trivial⟩, flat_not_evolvable⟩

/-- A subsingleton carrier admits no improvement: with one state, the goal is already
    an equilibrium of every dynamics, so `genuine` fails. The #12 counterpart of
    `no_understanding_of_subsingleton`. Profile: axiom-free. -/
theorem no_improvement_of_subsingleton {S : Type*} [Subsingleton S]
    (imp : Improvement S) : False :=
  imp.genuine (Subsingleton.elim _ _)

/-- A system at rest admits no improvement: if the native dynamics is the identity,
    every goal is already an equilibrium. Profile: axiom-free. -/
theorem no_improvement_of_id {S : Type*} (imp : Improvement S) (h : imp.dyn = id) :
    False :=
  imp.genuine (by show imp.dyn imp.goal = imp.goal; rw [h]; rfl)

/-! ## §B What the existing #6 ⇏ #12 witness actually fixes

  `evolvable_but_not_improvable` pairs `Evolvable (Fin 3)` (true by `Fin 3`'s order alone,
  §A) with "no directed agent whose understood dynamics is the 3-cycle". The evolving
  step (`fin3climb`) and the improved dynamics (`x ↦ x + 1`) are different maps on the
  same carrier; the 3-cycle is not itself an evolution step. And `Fin 3` does admit a
  directed agent for other dynamics. So the witness separates #6 from #12 *for that
  dynamics*, not carrier-wide. The carrier-wide form is §C. -/

/-- The 3-cycle is not a fitness-non-decreasing step under `Fin 3`'s order (`2 ↦ 0`
    descends), so it is not the step of any `Evolution (Fin 3)`.
    Profile: `propext`, `Classical.choice`, `Quot.sound` (decidability on `Fin 3`). -/
theorem cyclic3_not_evolution_step (e : Evolution (Fin 3)) :
    e.step ≠ fun x => x + 1 := by
  intro h
  have := e.selects 2
  rw [h] at this
  exact absurd this (by decide)

/-- An understanding of `Fin 3` collapsing to a reset: everything falls to `0`, and the
    model records only whether the state is at `0`. -/
def fin3ResetUnderstanding : Understanding (Fin 3) Bool where
  abstract := fun x => decide (x ≠ 0)
  systemDyn := fun _ => 0
  modelDyn := fun _ => false
  abstracts := fun _ => by decide
  surjective := fun b => by
    cases b
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
  compresses := by
    intro h
    have := @h 1 2 (by decide)
    exact absurd this (by decide)
  nontrivial := inferInstance

/-- `Fin 3` admits a directed agent (for the reset dynamics): evolvability of the carrier
    does not exclude directed improvement; only the 3-cycle dynamics does.
    Profile: `propext`, `Quot.sound`. -/
theorem fin3_directed_agent_exists : ∃ _ : DirectedAgent (Fin 3) Bool, True :=
  ⟨{ understanding := fin3ResetUnderstanding
     goal := 1
     intervene := fun _ => Function.const (Fin 3) 1
     improves := rfl
     genuine := by simp [IsEquilibrium, fin3ResetUnderstanding] }, trivial⟩

/-! ## §C Two-state carriers admit no understanding

  An understanding needs a surjection onto a nontrivial `M` that identifies two distinct
  states. With at most two states, identifying two of them makes `abstract` constant,
  so `M` collapses. Hence every carrier of size ≤ 2 separates any structure it does
  carry from #11 — and from `DirectedAgent`, which carries an understanding. -/

/-- No carrier with at most two states can be understood. The hypothesis says any three
    states contain a repeat (`|S| ≤ 2` without `Fintype`).
    Profile: `propext`, `Classical.choice`, `Quot.sound` (via `Function.not_injective_iff`). -/
theorem no_understanding_of_le_two {S M : Type*} (u : Understanding S M)
    (h : ∀ a b c : S, a = b ∨ b = c ∨ a = c) : False := by
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp u.compresses
  have hconst : ∀ x, u.abstract x = u.abstract a := by
    intro x
    rcases h a b x with hab' | hbx | hax
    · exact absurd hab' hne
    · rw [← hbx, hab]
    · rw [hax]
  haveI := u.nontrivial
  obtain ⟨m₁, m₂, hm⟩ := exists_pair_ne M
  obtain ⟨c₁, hc₁⟩ := u.surjective m₁
  obtain ⟨c₂, hc₂⟩ := u.surjective m₂
  exact hm (by rw [← hc₁, ← hc₂, hconst c₁, hconst c₂])

/-- `Bool` cannot be understood. Profile: `propext`, `Classical.choice`, `Quot.sound`. -/
theorem no_understanding_of_bool {M : Type*} (u : Understanding Bool M) : False :=
  no_understanding_of_le_two u (by decide)

/-- `Bool` is evolvable under its own order (`false < true`). Profile: `propext`,
    `Classical.choice`, `Quot.sound`. -/
theorem bool_evolvable : Evolvable Bool :=
  evolvable_iff_exists_lt.mpr ⟨false, true, by decide⟩

/-- **#6 ⇏ #11.** `Bool` is evolvable and, for every dynamics, not understandable.
    Profile: `propext`, `Classical.choice`, `Quot.sound`. -/
theorem evolvable_not_understandable :
    Evolvable Bool ∧ (∀ (M : Type), Understanding Bool M → False) :=
  ⟨bool_evolvable, fun _ u => no_understanding_of_bool u⟩

/-- **#6 ⇏ #12, carrier-wide, `DirectedAgent` form.** `Bool` is evolvable and admits no
    directed agent for any dynamics (a directed agent carries an understanding). Stronger
    than `evolvable_but_not_improvable` in quantifying over all dynamics, weaker in that
    `Improvement Bool` (the bare form) does exist — see `improvable_not_understandable`.
    Profile: `propext`, `Classical.choice`, `Quot.sound`. -/
theorem evolvable_not_directed :
    Evolvable Bool ∧ (∀ (M : Type), DirectedAgent Bool M → False) :=
  ⟨bool_evolvable, fun _ a => no_understanding_of_bool a.understanding⟩

/-- A homeostat on `Bool` reading itself and toggling on error. -/
def boolHomeostat : Homeostat Bool Bool where
  setPoint := true
  sensor := id
  error := fun o t => o != t
  correct := fun e s => if e then !s else s

/-- **#8 ⇏ #11.** `Bool` carries a homeostat and no understanding: governance does not
    presuppose an understanding of the governed system.
    Profile: `propext`, `Classical.choice`, `Quot.sound`. -/
theorem homeostat_not_understanding :
    (∃ _ : Homeostat Bool Bool, True) ∧ (∀ (M : Type), Understanding Bool M → False) :=
  ⟨⟨boolHomeostat, trivial⟩, fun _ u => no_understanding_of_bool u⟩

/-- **#12 (bare) ⇏ #11.** `Bool` is improvable and not understandable. The ledger records
    "#12 presupposes #11, by the encoding" — this shows the presupposition lives in
    `DirectedAgent`'s `understanding` field, not in `Improvement`: an intervention with an
    external goal needs no compressed model of the system.
    Profile: `propext`, `Classical.choice`, `Quot.sound`. -/
theorem improvable_not_understandable :
    (∃ _ : Improvement Bool, True) ∧ (∀ (M : Type), Understanding Bool M → False) :=
  ⟨⟨boolImprovement true, trivial⟩, fun _ u => no_understanding_of_bool u⟩

/-! ## §D #11 ⇏ #12: an understood system at rest cannot be improved -/

/-- An understanding of `Fin 3` at rest: the identity dynamics, with the model recording
    whether the state is at `0`. -/
def fin3RestUnderstanding : Understanding (Fin 3) Bool where
  abstract := fun x => decide (x ≠ 0)
  systemDyn := id
  modelDyn := id
  abstracts := fun _ => rfl
  surjective := fun b => by
    cases b
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
  compresses := by
    intro h
    have := @h 1 2 (by decide)
    exact absurd this (by decide)
  nontrivial := inferInstance

/-- **#11 ⇏ #12.** `Fin 3` at rest is understood (`fin3RestUnderstanding`) and admits no
    directed agent for that dynamics: every goal is already an equilibrium, so no
    intervention is genuine. Same dynamics-fixed shape as `evolvable_but_not_improvable`.
    Profile: `propext`. -/
theorem understandable_not_improvable :
    (∃ _ : Understanding (Fin 3) Bool, True) ∧
      (∀ (M : Type) (a : DirectedAgent (Fin 3) M),
        a.understanding.systemDyn = id → False) :=
  ⟨⟨fin3RestUnderstanding, trivial⟩, fun _ a h => no_improvement_of_id a.toImprovement h⟩

/-! ## §E The dashed 9 → 11 arrow, forgetful direction

  The reading edition (§6) says "#11 ⟹ #9 is by forgetting `compresses` and
  `nontrivial`". Here is that map. The roles swap: an understanding is a homomorphism
  *out of* the system (`abstract : S → M`), an internal model a homomorphism *into* it
  (`model : R → S`); so the understood system occupies the modeller slot `R` and the
  compressed model occupies the system slot `S`. K ≅ **2** again: one arrow, read from
  either end. -/

/-- Every understanding is an internal model with the roles swapped: the coarse-graining
    is the modelling map. Profile: axiom-free. -/
def Understanding.toInternalModel {S M : Type*} (u : Understanding S M) :
    InternalModel S M where
  model := u.abstract
  internalDyn := u.systemDyn
  systemDyn := u.modelDyn
  simulates := u.abstracts

/-- The forgetful map preserves the modelling map and both dynamics. Profile: axiom-free. -/
theorem Understanding.toInternalModel_model {S M : Type*} (u : Understanding S M) :
    u.toInternalModel.model = u.abstract ∧
      u.toInternalModel.internalDyn = u.systemDyn ∧
      u.toInternalModel.systemDyn = u.modelDyn :=
  ⟨rfl, rfl, rfl⟩

/-! ## §F #4 ⇏ #8

  NOT SEPARABLE as structures. `Homeostat S O` has four fields and no law; given any
  inhabited `O` it is inhabited on every carrier (`Homeostat.ofLaw`, §G). Likewise
  `GovernanceSubsystem` is inhabited whenever a `ConcreteSystem` and an `O` are. No
  carrier with a dynamics lacks a homeostat, so no witness of the header's shape exists.

  The weaker true thing, in the shape of `goal_is_external`: the feedback law does not
  determine the set-point. Two homeostats, one law, two set-points. This uses a
  target-blind `error` (it ignores the set-point), so it shows only that `Homeostat`
  carries a field its law does not fix — not that governance "adds" content in any
  dynamical sense. The ledger's wording stands: "governance carries data coupled
  dynamics does not", not "#4 ⇏ #8". -/

/-- A homeostat whose error ignores the set-point. -/
def targetBlindHomeostat (sp : Bool) : Homeostat Bool Bool where
  setPoint := sp
  sensor := id
  error := fun o _ => o
  correct := fun _ s => s

/-- **The set-point is not a function of the feedback law** (weak witness; see §F).
    Profile: axiom-free. -/
theorem setPoint_not_determined_by_law :
    ∃ h₁ h₂ : Homeostat Bool Bool,
      h₁.feedbackLaw = h₂.feedbackLaw ∧ h₁.setPoint ≠ h₂.setPoint :=
  ⟨targetBlindHomeostat true, targetBlindHomeostat false, rfl, by decide⟩

/-! ## §G Non-separability constructions for the remaining arrows

  Each def below builds the target structure on an arbitrary carrier from the source's
  data (or from nothing). Where such a def exists, the converse pair cannot be witnessed
  in the header's sense, and this is the proof of that. -/

/-- **1 → 4, converse NOT SEPARABLE.** Every concrete system is the system of a dynamic
    system: choose any state space and the identity law. #4's data (state space, law)
    is free over #1. Profile: axiom-free. -/
def ConcreteSystem.toStaticDynamics {α : Type*} [ActsOn α] (σ : ConcreteSystem α)
    (S : Type*) : DynamicSystem α S where
  system := σ
  law := id

/-- **8 → 12, converse NOT SEPARABLE.** Every self-map is the feedback law of a homeostat
    (trivial observable, correction ignoring the error). An improvement's `intervene dyn`
    is therefore always realized by some homeostat, so no carrier is improvable and
    homeostat-free. Profile: axiom-free. -/
def Homeostat.ofLaw {S : Type*} (f : S → S) : Homeostat S Unit where
  setPoint := ()
  sensor := fun _ => ()
  error := fun _ _ => ()
  correct := fun _ => f

/-- `Homeostat.ofLaw` recovers the law it was built from. Profile: axiom-free. -/
theorem Homeostat.ofLaw_feedbackLaw {S : Type*} (f : S → S) :
    (Homeostat.ofLaw f).feedbackLaw = f :=
  rfl

/-- **9 → 8, converse NOT SEPARABLE.** `InternalModel.refl f : InternalModel S S` exists
    for every dynamics `f` (Understanding.lean:155): every system models itself. Nothing
    ⇏ #9 can be witnessed; #9's content is the theorem `tracks`, not the existence of an
    instance. Restated here so the file names it. Profile: axiom-free. -/
theorem internalModel_always_exists {S : Type*} (f : S → S) :
    ∃ _ : InternalModel S S, True :=
  ⟨InternalModel.refl f, trivial⟩

/-! **3 → 8, no Lean home.** `GovernanceSubsystem` (Governance.lean:119) carries
  `system : ConcreteSystem α` — #1's structure — and no `FlowNetwork`. `FlowNetwork`
  lives in `Systems/Mobus/FlowNetwork.lean`, which `Systems/Core/Governance.lean` does
  not import. The DAG's "flow network" label on 3 → 8 has no field or theorem behind
  it; the arrow that does exist is 1 → 8 (through the `system` field). NOT SEPARABLE in
  either direction (different carriers), and the arrow itself should be redrawn or
  labelled as prose.

  **5 → 11, prose.** `SameKind` (#5) is a relation on components under `ActsOn`;
  `Understanding` (#11) is on a state space with no `ActsOn`. No shared carrier, no
  theorem; the reading edition already lists this arrow as conjecture (§9).

  **4 → 9 (solid), converse.** `InternalModel R S` is a `Function.Semiconj` over plain
  functions and needs no `ConcreteSystem`; #4's structure needs one. Different carriers;
  a "#9 ⇏ #4" witness would need a state space with no concrete system, which is a
  category error rather than a separation.

  **9 → 10, 9 → 7 (solid).** Derived notions (`SelfModel.toInternalModel`,
  `FastSelfModel.toAnticipatory`, `InternalModel.toChannel`); converses are not
  independence claims and are not attempted. -/

/-! ## §H #5 derives from #1 and #2 by imports; #3 enters only as `structure'`

  `Systems/Core/Complexity.lean` has exactly one import: `Systems.Core.Systemness`.
  Transitively: `Systems.Core.Systemness` → `Systems.Core.System`, `Systems.Core.Level`;
  `Systems.Core.System` → `Systems.Core.Bond` → `Systems.Core.Thing`.
  `Systems.Mobus.FlowNetwork` (#3's structure) is NOT in that closure. The "Networks #3"
  row of Complexity's derivability table refers to `ConcreteSystem.internalStructure`,
  which is the `structure' : Set (α × α)` field of #1's structure (System.lean:98), not
  a `FlowNetwork`. Honest wording: **#5 is definable from #1 (`ActsOn`, `ConcreteSystem`)
  and #2 (`RecursiveSystem.depth` via Level); the relational data Mobus calls "network"
  is already a field of #1.** Nothing in `sameKind_equivalence` touches #3's file. -/

end Systems
