import Lake
open Lake DSL

package «CuFunTheory» where
  name := "CuFunTheory"

require mathlib from git "https://github.com/leanprover-community/mathlib4"

lean_lib «CuFunTheory» where
  roots := #[`CuFunTheory]
