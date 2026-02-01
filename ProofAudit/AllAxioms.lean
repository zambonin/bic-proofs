import GenericRankingBic
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom dependencies of all library theorems, including generated declarations. -/

open Lean Elab Command
set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
run_cmd do
  let env ← getEnv
  let sourceDir : System.FilePath := "GenericRankingBic"
  if ← sourceDir.pathExists then
    for path in ← sourceDir.walkDir do
      if path.extension == some "lean" then
        let mod := (path.withExtension "").components.foldl Name.str .anonymous
        unless env.header.moduleNames.contains mod do
          throwError "Library module missing from root imports: {mod}"
  let mut roots : Array Name := #[]
  let modules := env.header.moduleNames.map fun mod =>
    mod.toString == "GenericRankingBic" || mod.toString.startsWith "GenericRankingBic."
  for (name, index) in env.const2ModIdx.toArray do
    if modules[index.toNat]! then
      if let some (.thmInfo _) := env.find? name then
        roots := roots.push name
  let action : CollectAxioms.M Unit := roots.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  let extras := state.axioms.filter fun ax =>
    !([`propext, `Classical.choice, `Quot.sound].contains ax)
  if !extras.isEmpty then
    throwError "Unpermitted axiom dependencies: {extras}"
  logInfo m!"Checked {roots.size} library theorem declarations."
  logInfo m!"Axiom dependencies: {state.axioms}"
