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

-- Phase 2: Mobus 8-tuple
import Systems.Mobus.FlowNetwork
import Systems.Mobus.Environment
import Systems.Mobus.Boundary
import Systems.Mobus.Interface
import Systems.Mobus.Tuple
import Systems.Mobus.Bridge
import Systems.Mobus.Composition

-- Phase 3: Klir common root
import Systems.Klir.KlirSystem
import Systems.Klir.ViewGeneration
import Systems.Klir.SpivakSystem

-- Categorification: shape categories + common core theorem
import Systems.Category.SubsystemCategory
import Systems.Category.FlattenFunctor
import Systems.Category.OrderingTriangle
import Systems.Category.BridgeFunctor
import Systems.Category.ShapeKlir
import Systems.Category.ShapeBunge
import Systems.Category.ShapeMobus
import Systems.Category.ShapeMyers
import Systems.Category.ShapeWymore
import Systems.Category.ShapeMesarovic
import Systems.Category.ShapeJoslyn
import Systems.Category.ShapeSpivak
import Systems.Category.ShapeWillems
import Systems.Category.ShapeComparison
import Systems.Category.ShapeComparison_Myers
import Systems.Category.ShapeComparison_Wymore
import Systems.Category.Diagram
import Systems.Category.CommonCore
