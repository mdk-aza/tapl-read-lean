import Lake
open Lake DSL

package «type-systems-in-lean» where
  version := v!"0.1.0"
  defaultTargets := #[`TypeSystemsInLean]

  lean_lib TypeSystemsInLean where
    globs := #[Glob.submodules `TypeSystemsInLean]

    require mathlib from git
    "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"