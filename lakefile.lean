import Lake
open Lake DSL

package «ModalThesis» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

@[default_target]
lean_lib «ModalThesis» where
  srcDir := "lean"

lean_exe modal_thesis_spiral_dump where
  root := `ModalThesis.CLI.SpiralDumpMain
  srcDir := "lean"
