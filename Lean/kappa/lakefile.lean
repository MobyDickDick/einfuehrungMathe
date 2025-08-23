import Lake
open Lake DSL

package «kappa» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib «Kappa» where
  globs := #[.submodules `Kappa]
