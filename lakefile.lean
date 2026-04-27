import Lake
open Lake DSL

package «adic_lean_proof_replay» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

@[default_target]
lean_lib «ADIC_RSound_Replay» where
