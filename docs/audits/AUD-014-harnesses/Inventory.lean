import MhfeCore
import Lean

open Lean

namespace MhfeCodeAudit

/-- Select all declarations by source module, including global-name external models/private helpers. -/
def target (env : Environment) (declaration : Name) : Bool :=
  match env.getModuleIdxFor? declaration with
  | some index =>
      let moduleName := env.header.moduleNames[index.toNat]!.toString
      moduleName == "MhfeCore" || moduleName.startsWith "MhfeCore."
  | none => declaration.toString.startsWith "MhfeProofs.Audit"

/-- Check all active local definitions and their transitive axioms, not only the author's list. -/
def report : CoreM Unit := do
  let env ← getEnv
  let roots := env.constants.fold (init := #[]) fun acc declaration _ =>
    if target env declaration then acc.push declaration else acc
  unless !roots.isEmpty do
    throwError "No implementation-proof declarations were selected"
  let mut ownAxioms := #[]
  let mut axioms : NameSet := {}
  let mut theorems := #[]
  let mut byModule : Std.HashMap String Nat := {}
  let mut theoremAxioms : Array Json := #[]
  for declaration in roots do
    unless (env.checked.get.find? declaration).isSome do
      throwError "Unchecked declaration: {declaration}"
    if let some (.axiomInfo _) := env.find? declaration then
      ownAxioms := ownAxioms.push declaration
    let closure ← collectAxioms declaration
    for axiomName in closure do
      axioms := axioms.insert axiomName
    if let some (.thmInfo _) := env.find? declaration then
      theorems := theorems.push declaration
      theoremAxioms := theoremAxioms.push <| Json.mkObj [
        ("name", toJson declaration.toString), ("axioms", toJson (closure.map Name.toString))]
    if let some index := env.getModuleIdxFor? declaration then
      let key := env.header.moduleNames[index.toNat]!.toString
      byModule := byModule.insert key (byModule.getD key 0 + 1)
  unless ownAxioms.isEmpty do
    throwError "Local axioms are forbidden: {ownAxioms}"
  let closure := axioms.toArray.qsort Name.lt
  let unexpected := closure.filter fun declaration =>
    declaration != `propext && declaration != `Classical.choice && declaration != `Quot.sound
  unless unexpected.isEmpty do
    throwError "Unexpected proof axioms: {unexpected}"
  let value := Json.mkObj [
    ("roots", toJson ((roots.qsort Name.lt).map Name.toString)),
    ("theorems", toJson ((theorems.qsort Name.lt).map Name.toString)),
    ("axioms", toJson (closure.map Name.toString)),
    ("localAxioms", toJson (ownAxioms.map Name.toString)),
    ("byModule", Json.mkObj (byModule.toList.map fun (key, count) => (key, toJson count))),
    ("theoremAxioms", toJson theoremAxioms)]
  IO.FS.writeFile "axiom-inventory.json" value.compress
  logInfo m!"MHFE_CODE_AXIOM_INVENTORY|{roots.size}|{theorems.size}|standard"

end MhfeCodeAudit

#eval MhfeCodeAudit.report
