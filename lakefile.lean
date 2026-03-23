import Lake
open Lake DSL

package «tapl-read-lean» where
  version := v!"0.1.0"
  defaultTargets := #[`TaplLean]

lean_lib TaplLean where
  globs := #[Glob.submodules `TaplLean]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"