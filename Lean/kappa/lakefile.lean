import Lake
open Lake DSL

package «kappa» where

-- mathlib einbinden:
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "stable"

@[default_target]
lean_lib «Kappa» where
  -- optional
