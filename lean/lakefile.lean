import Lake
open Lake DSL

package sarkozy where
  version := v!"0.1.0"
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`warningAsError, true⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "c55e6e786f49471c72fbddbec5415808896aec1e"

@[default_target] lean_lib Sarkozy
