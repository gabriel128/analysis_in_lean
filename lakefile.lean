import Lake
open Lake DSL

package «analysis_in_lean» {
  -- add package configuration options here
}

lean_lib «AnalysisInLean» {
  -- add library configuration options here
}

lean_lib Natu

@[default_target]
lean_exe «analysis_in_lean» {
  root := `Main
}

require std4 from git "https://github.com/leanprover/std4"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
