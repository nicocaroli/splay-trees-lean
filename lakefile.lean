import Lake
open Lake DSL

package «splay-tree» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «SplayTree» {
  -- add any library configuration options here
}
lean_lib Definitions
lean_lib Delete
lean_lib ForallKeys
lean_lib Insert
lean_lib Join
lean_lib Lookup
lean_lib Splay
lean_lib Split
