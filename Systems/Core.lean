/-
  Systems/Core.lean — Imports all core systems ontology modules.

  Import order follows the dependency graph:
    Thing → Bond → System → Level, Assembly, Selection, State
-/
import Systems.Core.Thing
import Systems.Core.Bond
import Systems.Core.System
import Systems.Core.Level
import Systems.Core.Assembly
import Systems.Core.Selection
import Systems.Core.State
import Systems.Core.Systemness
import Systems.Core.Complexity
import Systems.Core.Dynamics
import Systems.Core.Lens
import Systems.Core.Governance
