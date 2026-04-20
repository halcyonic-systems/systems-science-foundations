/-
  Systems/Examples/Thermostat.lean
  Joslyn's thermostat formalized under Klir, Bunge, and Mobus

  The thermostat is the canonical control₂ example from Joslyn (1995,
  "Semantic Control Systems," Proposition 29). We formalize it under
  all three frameworks to demonstrate the commuting triangle on a
  concrete instance.

  Modeling decisions:
  - Components C = {thermometer, controller, furnace}
  - Environment E = {room, outsideAir}
  - Interfaces I = {thermometer, furnace}
  - room is environment: the thermostat acts ON the room
  - outsideAir is environment: its thermal effect is ambient (milieu)
  - Capacity κ = Unit (structural proofs don't depend on capacity)
-/

import Systems.Klir.KlirSystem

namespace Systems.Examples

/-! ## Entity Type -/

inductive Entity where
  | thermometer
  | controller
  | furnace
  | room
  | outsideAir
  deriving DecidableEq

open Entity

/-! ## Action Relation -/

instance entityActsOn : ActsOn Entity where
  actsOn
    | room, thermometer => True
    | thermometer, controller => True
    | controller, furnace => True
    | furnace, room => True
    | _, _ => False

/-! ## Shared Definitions -/

def comps : Set Entity := {thermometer, controller, furnace}
def envObjs : Set Entity := {room, outsideAir}
def intfs : Set Entity := {thermometer, furnace}

/-! ## Internal Flow Network -/

def intEdges : Set (FlowEdge Entity Unit) :=
  fun e => (e.source = thermometer ∧ e.target = controller ∧ e.capacity = ())
         ∨ (e.source = controller ∧ e.target = furnace ∧ e.capacity = ())

def intNet : FlowNetwork Entity Unit where
  nodes := comps
  edges := intEdges
  edges_on := by
    intro e he
    rcases he with ⟨hs, ht, _⟩ | ⟨hs, ht, _⟩
    · constructor
      · rw [hs]; show thermometer ∈ comps; left; rfl
      · rw [ht]; show controller ∈ comps; right; left; rfl
    · constructor
      · rw [hs]; show controller ∈ comps; right; left; rfl
      · rw [ht]; show furnace ∈ comps; right; right; rfl
  no_self_loops := by
    intro e he
    rcases he with ⟨hs, ht, _⟩ | ⟨hs, ht, _⟩ <;> (rw [hs, ht]; decide)

/-! ## External Flow Network -/

def extEdges : Set (FlowEdge Entity Unit) :=
  fun e => (e.source = room ∧ e.target = thermometer ∧ e.capacity = ())
         ∨ (e.source = furnace ∧ e.target = room ∧ e.capacity = ())

def extNet : FlowNetwork Entity Unit where
  nodes := ({room, thermometer, furnace} : Set Entity)
  edges := extEdges
  edges_on := by
    intro e he
    rcases he with ⟨hs, ht, _⟩ | ⟨hs, ht, _⟩
    · exact ⟨by rw [hs]; left; rfl,
             by rw [ht]; right; left; rfl⟩
    · exact ⟨by rw [hs]; right; right; rfl,
             by rw [ht]; left; rfl⟩
  no_self_loops := by
    intro e he
    rcases he with ⟨hs, ht, _⟩ | ⟨hs, ht, _⟩ <;> (rw [hs, ht]; decide)

/-! ## Helper: Disjointness -/

private theorem comps_envObjs_disjoint : comps ∩ envObjs = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hc he
  unfold comps at hc; unfold envObjs at he
  rcases hc with rfl | rfl | rfl <;> (rcases he with h | h <;> exact nomatch h)

/-! ## Mobus 8-Tuple -/

def thermostatMobus : MobusSystem Entity Unit Unit Unit Unit Unit Unit where
  components := comps
  internalNetwork := intNet
  environment := ⟨envObjs, ()⟩
  externalFlows := extNet
  boundary := ⟨(), intfs⟩
  transforms := ()
  history := ()
  timeScale := ()
  network_components := rfl
  disjoint := comps_envObjs_disjoint
  interfaces_sub := by
    intro x hx
    show x ∈ comps
    rcases hx with rfl | rfl
    · left; rfl
    · right; right; rfl
  bipartite := by
    intro e he
    rcases he with ⟨hs, ht, _⟩ | ⟨hs, ht, _⟩
    · left
      exact ⟨by rw [hs]; show room ∈ envObjs; left; rfl,
             by rw [ht]; show thermometer ∈ intfs; left; rfl⟩
    · right
      exact ⟨by rw [hs]; show furnace ∈ intfs; right; rfl,
             by rw [ht]; show room ∈ envObjs; left; rfl⟩
  externalFlows_nodes := by
    intro x hx
    show x ∈ envObjs ∪ intfs
    rcases hx with rfl | rfl | rfl
    · left; left; rfl
    · right; left; rfl
    · right; right; rfl

/-! ## Flow-Action Consistency -/

theorem thermostat_flow_induces_action :
    FlowInducesAction intNet := by
  intro e he
  show e.source ▷ e.target
  rcases he with ⟨hs, ht, _⟩ | ⟨hs, ht, _⟩ <;> (rw [hs, ht]; trivial)

theorem thermostat_internal_nonempty :
    intNet.edges.Nonempty :=
  ⟨⟨thermometer, controller, ()⟩, Or.inl ⟨rfl, rfl, rfl⟩⟩

/-! ## Klir and Bunge Systems (from Mobus projections)

  Rather than defining these independently, we extract them from the
  Mobus 8-tuple via the projection maps. This ensures definitional
  equality with the projected systems. -/

def thermostatBunge : ConcreteSystem Entity :=
  thermostatMobus.toBunge
    thermostat_flow_induces_action
    thermostat_internal_nonempty

def thermostatKlir : KlirSystem Entity :=
  thermostatMobus.toKlir

/-! ## The Commuting Triangle on This Instance

  The central result: both paths from the Mobus thermostat to Klir
  produce definitionally identical systems.

  ```
        toBunge
  Mobus -------→ Bunge
    \              |
     \  toKlir    | toKlir
      \           |
       ↘          ↓
         Klir
  ``` -/

theorem thermostat_triangle_commutes :
    thermostatBunge.toKlir = thermostatKlir := rfl

/-! ## What Each Framework Captures

  Unpacking the projections reveals what information lives at each level:

  - thermostatKlir.things = {thermometer, controller, furnace}
    (just the components — environment entities lost)

  - thermostatKlir.relation = intNet.toRelation ∪ extNet.toRelation
    (all causal pairs including cross-boundary — but room appears in
    relation without appearing in things)

  - thermostatBunge adds: environment = {room, outsideAir}
    (now we know which entities are "outside")

  - thermostatMobus adds: milieu, capacity labels, boundary properties,
    transforms (the control rule), history, time scale
    (the engineering detail that Bunge's philosophical ontology omits) -/

end Systems.Examples
