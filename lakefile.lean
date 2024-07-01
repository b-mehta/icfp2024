import Lake
open Lake DSL

package «ICFP2024» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «ICFP2024» where
  -- add any library configuration options here

@[default_target]
lean_exe communicate where
  root := `ICFP2024

@[default_target]
lean_exe lambdatest where
  srcDir := "ICFP2024"
  root := `Lambdaman
