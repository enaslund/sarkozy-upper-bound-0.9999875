module

public import Sarkozy
public import Lean.Util.CollectAxioms

/-! Generate the precise declaration roots for an independent kernel export.
Only mathematical declarations in the project namespace are selected; their
transitive dependencies are then selected by lean4export itself. -/

open Lean Elab Command in
run_cmd do
  let mut names : Array String := #[]
  for (name, info) in (← getEnv).constants do
    if (`Sarkozy).isPrefixOf name && !info.isUnsafe && !info.isPartial then
      names := names.push name.toString
  names := names.qsort (· < ·)
  IO.FS.writeFile ".lake/export-declarations.txt" (String.intercalate "\n" names.toList ++ "\n")
  logInfo m!"Selected {names.size} Sarkozy declarations for independent export."
