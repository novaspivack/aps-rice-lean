import Lake
open Lake DSL

package «aps-rice» where
  -- Abstract formalization of recursion, Rice, halting for representability-restricted APS

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc3"

@[default_target]
lean_lib «APS» where
