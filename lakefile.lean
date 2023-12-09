import Lake
open Lake DSL

package «EG» {
  -- add any package configuration options here
}

@[default_target]
lean_lib «EuclideanGeometry» {
  -- add any library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

meta if get_config? env = some "CI_BUILD" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git" @ "3cc5df1be7f6db5ac13f26edda3fc258e199ab5f"
