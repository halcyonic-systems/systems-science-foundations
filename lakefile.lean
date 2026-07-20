import Lake
open Lake DSL

package «systems-ontology» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩  -- Force explicit universe/variable declarations
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Systems» where
  srcDir := "."
  roots := #[`Systems]

-- Rung 1.5 subprocess oracle (bert-lenses#24): JSON (T, R) model on stdin,
-- gate + mode verdicts on stdout. Built by `lake build` so CI catches any drift.
@[default_target]
lean_exe «gates-oracle» where
  root := `Systems.Klir.GatesOracle
