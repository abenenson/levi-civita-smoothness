import Lake
open Lake DSL

package «levi-civita-smoothness» where
  weakLeanArgs := #["-j1"]
  moreGlobalServerArgs := #["-j1"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
    "56a005855ea17e0b0958f73ec801ae140b0a1679"

@[default_target]
lean_lib MathlibExtensions

@[default_target]
lean_lib LeviCivitaSmoothness

