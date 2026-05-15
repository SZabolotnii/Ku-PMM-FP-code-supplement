import Lake
open Lake DSL

package PMM_FP where
  srcDir := "Lean"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0"

lean_lib PMM_FP where
  roots := #[`PMM_FP]
