/-
  Systems/Bunge/AggregateBridge.lean
  SSF #48 target 1 — the two aggregate criteria: bridge or separating instance.

  STATUS: In progress (scaffolded 2026-08-17). Build with:
    lake build Systems.Bunge.AggregateBridge

  Bunge gives two criteria for the aggregate/system distinction, and the repo
  currently encodes them on carriers that never meet:

    (1) BOND criterion (Ont. II Def 1.1 / Ont. I Cor 5.14):
        a collection is an aggregate iff it has no internal bonds.
        Encoded: Systems/Core/Systemness.lean `IsAggregate : Set α → Prop`.

    (2) STATE-SPACE criterion (Ont. II §2.2, "p. 640"; Ont. I Def 5.35):
        a thing is an aggregate iff its total state space equals the union
        of its components' state spaces.
        Encoded: Systems/Core/State.lean
        `isAggregate : Set S → List (Set S) → Prop`.

  Bunge asserts the criteria coextensive (Ont. I claims the derivation at
  Cor 5.14). No theorem in the repo links them, and the two theorems that
  exist (`aggregate_not_system`, `system_not_aggregate`) relate (2) only to
  its own literal negation — they could not have come out false.

  This file ties the carriers together (`StatefulComposite`) and settles the
  relationship. Expected outcome (to be confirmed by the proofs below): the
  criteria are logically INDEPENDENT as formalized — nothing in the ontology
  as encoded ties bonds to state spaces — so Cor 5.14's content is exactly a
  pair of unstated coupling postulates, named below as axiom candidates and
  NOT asserted.
-/

import Systems.Core.Bond
import Systems.Core.State
import Systems.Core.Systemness
import Mathlib.Data.Set.Lattice

namespace Systems

/- PROOF TARGET: the bond criterion and the state-space criterion for
   "aggregate" are logically independent over composites carrying both a
   bond relation and a state-space assignment.

   MATHEMATICAL INTENT:
   Bunge's two systemhood criteria are asserted equivalent (Ont. I Cor 5.14).
   If they are independent as encoded, the equivalence is not ontology but a
   substantive physical postulate (bonding restricts joint state), which must
   enter as a named axiom, not a silent assumption. Either outcome retires
   the standing vacuity in State.lean.

   AVAILABLE TOOLS:
   `ActsOn`, `Bonded` (Systems/Core/Bond.lean), `IsOrganized`, `IsAggregate`
   (Systems/Core/Systemness.lean), `isAggregate`, `isSystemByStateSpace`
   (Systems/Core/State.lean), `Set.foldl` union machinery, Mathlib set lattice.

   DOES NOT COUNT:
   - witnesses on an empty or one-point carrier (the criteria must disagree
     on a composite with at least two distinct things);
   - an `ActsOn` instance whose action relation is `fun _ _ => False` for the
     bonded-side witness (the bond must actually hold);
   - defining the coupling postulates and then "proving" equivalence from
     them (that is restating the hypothesis, not a bridge);
   - `decide`/`native_decide` for the universal (independence) claims —
     concrete computation is fine for the ∃ witnesses only.

   STRATEGY HINT:
   Two finite witnesses over `Bool`-like carriers with hand-picked ActsOn
   instances; equivalence-under-coupling stated last as the repaired form.
-/

/-- A composite that carries BOTH criteria's data: a set of things with a
    bond relation (via `ActsOn α`), a state space for each thing, and a
    joint state space for the whole. The two aggregate criteria become
    predicates on one object, so their relationship is finally a theorem
    (or a counterexample) rather than a category error. -/
structure StatefulComposite (α : Type*) (S : Type*) [ActsOn α] where
  things : Set α
  stateOf : α → Set S
  totalSpace : Set S

namespace StatefulComposite

variable {α S : Type*} [ActsOn α]

/-- Criterion (1), bond form, imported from Systemness.lean. -/
def bondAggregate (c : StatefulComposite α S) : Prop :=
  IsAggregate c.things

/-- Criterion (2), state-space form. Stated with an indexed union over the
    composite's own things (the List-fold form in State.lean is equivalent
    for any enumeration; see `stateAggregate_foldl` below). -/
def stateAggregate (c : StatefulComposite α S) : Prop :=
  c.totalSpace = ⋃ x ∈ c.things, c.stateOf x

/-- Separating instance, direction one: a composite whose things are bonded
    (organized — criterion 1 says SYSTEM) while its joint state space is
    exactly the union of its parts' (criterion 2 says AGGREGATE).
    A bond with no state-space consequence: nothing in the encoded ontology
    forbids it. -/
theorem bonded_yet_stateAggregate :
    ∃ (α S : Type) (inst : ActsOn α) (c : @StatefulComposite α S inst),
      IsOrganized c.things ∧ c.stateAggregate := by
  letI inst : ActsOn Bool := ⟨fun a b => a = true ∧ b = false⟩
  refine ⟨Bool, Unit, inst,
    ⟨Set.univ, fun _ => Set.univ, Set.univ⟩, ?_, ?_⟩
  · exact ⟨true, Set.mem_univ _, false, Set.mem_univ _, by decide,
      Or.inl ⟨rfl, rfl⟩⟩
  · show Set.univ = ⋃ x ∈ (Set.univ : Set Bool), (Set.univ : Set Unit)
    ext u
    simp

/-- Separating instance, direction two: a composite with no internal bonds
    (criterion 1 says AGGREGATE) whose joint state space strictly exceeds
    the union of its parts' (criterion 2 says SYSTEM). Correlation without
    connection: the encoded ontology does not rule it out either. -/
theorem bondFree_yet_stateSystem :
    ∃ (α S : Type) (inst : ActsOn α) (c : @StatefulComposite α S inst),
      c.bondAggregate ∧ ¬c.stateAggregate := by
  letI inst : ActsOn Bool := ⟨fun _ _ => False⟩
  refine ⟨Bool, Bool, inst,
    ⟨Set.univ, fun _ => {false}, Set.univ⟩, ?_, ?_⟩
  · rintro ⟨a, -, b, -, -, hbond⟩
    rcases hbond with h | h <;> exact h
  · intro h
    have : (true : Bool) ∈ ⋃ x ∈ (Set.univ : Set Bool), ({false} : Set Bool) := by
      rw [← h]; exact Set.mem_univ _
    simp at this

/-- The verdict, packaged: neither criterion implies the other over
    StatefulComposite. Follows from the two witnesses. -/
theorem aggregate_criteria_independent :
    (¬ ∀ (α S : Type) (inst : ActsOn α) (c : @StatefulComposite α S inst),
        c.stateAggregate → c.bondAggregate) ∧
    (¬ ∀ (α S : Type) (inst : ActsOn α) (c : @StatefulComposite α S inst),
        c.bondAggregate → c.stateAggregate) := by
  constructor
  · intro hall
    obtain ⟨α, S, inst, c, horg, hstate⟩ := bonded_yet_stateAggregate
    exact hall α S inst c hstate horg
  · intro hall
    obtain ⟨α, S, inst, c, hbf, hss⟩ := bondFree_yet_stateSystem
    exact hss (hall α S inst c hbf)

/- AXIOM CANDIDATES (named, NOT asserted — per the no-silent-axioms rule):

   The two halves of Ont. I Cor 5.14's claimed equivalence, as explicit
   coupling postulates over StatefulComposite:

   couplingForward :  IsOrganized c.things → ¬c.stateAggregate
     "a bond shows up in the joint state space" — the physically substantive
     half; this is what Bunge's prose actually argues.

   couplingBackward : ¬c.stateAggregate → IsOrganized c.things
     "state correlation only from bonds" — a locality/no-conspiracy
     postulate Bunge never states.

   With both, bondAggregate ↔ stateAggregate is immediate (contrapositives).
   That immediacy is the point: the equivalence IS the postulate pair.
   Decision for the session: record as axiom candidates in the companion
   doc's table, or as hypotheses on a bridging theorem. Default: hypotheses.
-/

end StatefulComposite

end Systems
