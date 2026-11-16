import LeanChecker

namespace MhfeAudit

/-- Invoke the official checker's exact-module kernel replay sequentially. -/
unsafe def replay (modules : List Lean.Name) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  for module in modules do
    replayFromImports module
    IO.println s!"REPLAY_OK|{module}"

end MhfeAudit
