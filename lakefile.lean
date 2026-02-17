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
