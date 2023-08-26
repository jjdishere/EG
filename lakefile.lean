import Lake
open Lake DSL

package «EG» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «EuclideanGeometry» {
  -- add any library configuration options here
}
