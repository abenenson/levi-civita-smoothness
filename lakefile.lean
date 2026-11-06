import Lake
open Lake DSL

package «levi-civita-smoothness» where
  weakLeanArgs := #["-j1"]
  moreGlobalServerArgs := #["-j1"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
    "d13f23b723b8a846827a245b89c10fc7d3f11612"

@[default_target]
lean_lib MathlibExtensions

@[default_target]
lean_lib LeviCivitaSmoothness

