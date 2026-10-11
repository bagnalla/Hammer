import Lean

open Lean

namespace ProofAudit

/-- The complete policy; declaration names are discovered from the compiled environment. -/
def allowedAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

/-- Discover the root module and every source module beneath it, including nested directories. -/
def discoverModules (root : Name) : IO (Array Name) := do
  let path : System.FilePath := root.toString.replace "." "/"
  let mut files := #[]
  if ← (path.withExtension "lean").pathExists then
    files := files.push (path.withExtension "lean")
  if ← path.isDir then
    files := files ++ (← path.walkDir).filter (·.extension == some "lean")
  if files.isEmpty then
    throw <| IO.userError s!"No Lean source modules found for {root}"
  return files.map (fun file =>
    file.withExtension "" |>.components.foldl Name.str .anonymous) |>.qsort Name.lt

/-- Audit all declarations owned by the discovered modules, regardless of name or visibility. -/
def audit (modules : Array Name) : CoreM (Nat × Nat) := do
  let env ← getEnv
  for module in modules do
    unless (env.getModuleIdx? module).isSome do
      throwError "Axiom audit: module {module} was not imported"
  let mut targets := #[]
  for (name, info) in env.constants do
    if let some index := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[index.toNat]!
      if modules.contains owner then
        targets := targets.push (name, owner, info.isTheorem)
  if targets.isEmpty then
    throwError "Axiom audit: no declarations found in the discovered modules"
  targets := targets.qsort (fun a b => Name.lt a.1 b.1)
  let mut theorems := 0
  for (name, owner, isTheorem) in targets do
    let unexpected := (← collectAxioms name).filter (!allowedAxioms.contains ·)
    unless unexpected.isEmpty do
      throwError "Axiom audit: {name} (module {owner}) depends on unexpected axioms: {unexpected}"
    if isTheorem then
      theorems := theorems + 1
  return (targets.size, theorems)

end ProofAudit

/-- Run from the Lean source directory after building the modules. An optional root supports tests. -/
unsafe def main (args : List String) : IO Unit := do
  let root ← match args with
    | [] => pure `RustHammer
    | [root] => pure root.toName
    | _ => throw <| IO.userError "Usage: proof-audit [module-root]"
  let modules ← ProofAudit.discoverModules root
  initSearchPath (← findSysroot)
  enableInitializersExecution
  -- Private imports retain private helpers and their axiom dependency metadata.
  let env ← importModules (modules.map ({ module := · })) {} (loadExts := true) (level := .private)
  let ((declarations, theorems), _) ← Lean.Core.CoreM.toIO (ProofAudit.audit modules)
    { fileName := "<axiom-audit>", fileMap := default } { env }
  IO.println s!"Axiom audit: {declarations} declarations ({theorems} theorems) in \
    {modules.size} modules use only standard Lean axioms."
