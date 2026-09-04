/-
  Systems Ontology — Machine-verified systems science in Lean 4

  Root import. `import Systems` gives access to all modules:

  - Core/     Bunge CES triple + Principles formalization (#1-#5)
  - Mobus/    8-tuple, flows, boundary, bridge, composition
  - Klir/     Common root S=(T,R), commuting triangle
  - Category/ Shape categories (8 traditions), comparison functors, K ≅ 2

  See docs/INDEX.md for documentation reading order.
  See CLAUDE.md for dependency graph and conventions.
-/

-- Phase 1: Bunge foundations + Principles formalization
import Systems.Core
-- The twelve principles, front door: one re-export per principle + checked witnesses
import Systems.Principles
import Systems.Principles.Witnesses
import Systems.Principles.Matrix
import Systems.Principles.Hierarchy
import Systems.Principles.NonDegenerate

-- Phase 2: Mobus 8-tuple
import Systems.Mobus.FlowNetwork
import Systems.Mobus.Environment
import Systems.Mobus.Boundary
import Systems.Mobus.Interface
import Systems.Mobus.Tuple
import Systems.Mobus.Lifecycle
import Systems.Mobus.Bridge
import Systems.Mobus.Composition

-- Hierarchical decomposition by reference: the seam contract (bert-lenses#89)
import Systems.Core.Decomposition
import Systems.Core.InterfaceDecomposition
-- Component–state bridge, ADOPTED 2026-09-04 (dependent product over components and
-- flows; docs/reference/component-state-bridge-memo.md). The aggregate criterion is
-- `IsProductAggregate`; the union reading of Bunge p. 640 is retired, not deleted.
import Systems.Core.JointState
-- Bond criterion vs product criterion: independent both ways, Cor 5.14 as hypotheses
import Systems.Bunge.AggregateBridge

-- Mesarovic 1964: decomposition theorem cores (peel lemma + dyadic floor)
import Systems.Mesarovic.Decomposition

-- Phase 3: Klir common root
import Systems.Klir.KlirSystem
import Systems.Klir.ViewGeneration
import Systems.Klir.Gates
import Systems.Klir.GatesTruthTable
import Systems.Klir.SpivakSystem

-- Phase 4: Joslyn fourth vertex (set-theoretic tier, 4.1 + 4.3 + 4.4 + 4.5)
import Systems.Joslyn.JoslynSystem
import Systems.Joslyn.Control
import Systems.Joslyn.BungeMap
import Systems.Joslyn.HCGS

-- Categorification: shape categories + common core theorem
import Systems.Category.SubsystemCategory
import Systems.Category.FlattenFunctor
import Systems.Category.OrderingTriangle
import Systems.Category.BridgeFunctor
import Systems.Category.ShapeBertalanffy
import Systems.Category.ShapeKlir
import Systems.Category.ShapeBunge
import Systems.Category.ShapeMobus
import Systems.Category.ShapeMyers
import Systems.Category.ShapeWymore
import Systems.Category.ShapeMesarovic
import Systems.Category.ShapeJoslyn
import Systems.Category.CyclicObstruction
import Systems.Category.JoslynIncomparability
import Systems.Category.ShapeSpivak
import Systems.Category.MyersSpivakFaithful
import Systems.Category.SpivakIncomparability
import Systems.Category.ShapeWillems
import Systems.Category.ShapeComparison
import Systems.Category.ShapeComparison_Myers
import Systems.Category.ShapeComparison_Wymore
import Systems.Category.Diagram
import Systems.Category.CommonCore
import Systems.Category.SharedPrimitive

-- The declared Dynamics record: τ refined from opaque to a checkable 5-field
-- vocabulary (bert-lenses#112 / dynamics-position Q5; declaration only)
import Systems.Dynamics.Record
import Systems.Dynamics.Transition
import Systems.Dynamics.Mechanism
-- H at BERT's abstracted carrier (bert-lenses#112 §4): the recorded run
-- history is the finite prefix of the final-coalgebra observable behaviour
-- under the identity observer. Research-tier; not a Challenge.lean headline.
import Systems.Dynamics.CircuitHistory

-- Trusted statement file: the K ≅ 2 headline claims restated for cold
-- verification (comparator pattern). Check with scripts/check-challenge.sh.
import Systems.Challenge
