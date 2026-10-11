import Lake
open Lake DSL

require aeneas from git
  "https://github.com/AeneasVerif/aeneas" @
  "557eff83ecef5083b98a52a94ca7fae63d6c1dab" / "backends/lean"

package rusthammer where
  moreLeanArgs := #["-DwarningAsError=true", "-DautoImplicit=false"]

@[default_target]
lean_lib RustHammer where
  globs := #[.andSubmodules `RustHammer]

lean_exe «proof-audit» where
  root := `ProofAudit
  supportInterpreter := true
