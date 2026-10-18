import Lake
open Lake DSL

package venn37

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "520045ab14e26149ee970e2e617ca04b09bde5d6"

@[default_target]
lean_lib Venn37 where
  -- connectivity checks by kernel reduction need a deep stack
  moreLeanArgs := #["--tstack=4000000"]
