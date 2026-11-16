import MhfeLean
import Lean

open Lean
namespace TrialAudit

def target (env : Environment) (declaration : Name) : Bool :=
  match env.getModuleIdxFor? declaration with
  | some index =>
      let moduleName := env.header.moduleNames[index.toNat]!.toString
      moduleName == "MhfeLean" || moduleName.startsWith "MhfeLean."
  | none => declaration.toString.startsWith "MhfeLean.Audit"

def report : CoreM Unit := do
  let env ← getEnv
  let roots := env.constants.fold (init := #[]) fun acc declaration _ =>
    if target env declaration then acc.push declaration else acc
  unless !roots.isEmpty do
    throwError "No development declarations selected"
  let mut ownAxioms := #[]
  let mut axioms : NameSet := {}
  let mut theorems : Array Json := #[]
  for declaration in roots do
    unless (env.checked.get.find? declaration).isSome do
      throwError "Unchecked declaration: {declaration}"
    if let some (.axiomInfo _) := env.find? declaration then
      ownAxioms := ownAxioms.push declaration
    let closure ← collectAxioms declaration
    for axiomName in closure do
      axioms := axioms.insert axiomName
    if let some (.thmInfo _) := env.find? declaration then
      theorems := theorems.push <| Json.mkObj [
        ("name", toJson declaration.toString), ("axioms", toJson (closure.map Name.toString))]
  unless ownAxioms.isEmpty do
    throwError "Local axioms are forbidden: {ownAxioms}"
  let closure := axioms.toArray.qsort Name.lt
  let unexpected := closure.filter fun declaration =>
    declaration != `propext && declaration != `Classical.choice && declaration != `Quot.sound
  unless unexpected.isEmpty do
    throwError "Unexpected proof axioms: {unexpected}"
  let value := Json.mkObj [
    ("roots", toJson ((roots.qsort Name.lt).map Name.toString)),
    ("theoremAxioms", toJson theorems),
    ("axioms", toJson (closure.map Name.toString)),
    ("localAxioms", toJson (ownAxioms.map Name.toString))]
  IO.FS.writeFile "audit-inventory.json" value.compress
  logInfo m!"AUD016_FULL_SOURCE_INVENTORY|{roots.size}|{theorems.size}|standard"

end TrialAudit
#eval TrialAudit.report
