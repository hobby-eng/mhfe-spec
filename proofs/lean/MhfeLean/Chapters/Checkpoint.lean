import MhfeLean.Chapters.Feistel
import MhfeLean.Chapters.OracleModel
import MhfeLean.Chapters.Probability
import MhfeLean.Chapters.ChainMonitoring
import MhfeLean.Chapters.ChainEarly
import MhfeLean.Chapters.ChainCompletion
import MhfeLean.Chapters.ShortSources
import MhfeLean.Chapters.KnownPairResampling
import MhfeLean.Chapters.KnownPairCross
import MhfeLean.Chapters.KnownPairEarly
import MhfeLean.Chapters.KnownPairBound
import MhfeLean.Chapters.PasswordPairs
import MhfeLean.Chapters.GenerationSampling
import MhfeLean.Chapters.GenerationCoupling
import MhfeLean.Chapters.GenerationSurvival
import MhfeLean.Chapters.GenerationBound
import MhfeLean.Chapters.WalletResampling
import MhfeLean.Chapters.WalletCollision
import MhfeLean.Chapters.SeedPairs
import MhfeLean.Chapters.WalletSource
import MhfeLean.Chapters.CreationRefusal
import MhfeLean.Chapters.WalletRecovery
import MhfeLean.Chapters.OrdinaryWallet
import MhfeLean.Chapters.JointCost
import MhfeLean.Chapters.BatchQueries
import MhfeLean.Chapters.MatchingAttack
import MhfeLean.Chapters.WalletData
import MhfeLean.Chapters.WalletMatching
import MhfeLean.Chapters.DerivedWalletMatching
import MhfeLean.Chapters.Deniability
import MhfeLean.Chapters.KnownPairAttack
import MhfeLean.Chapters.DeniabilityGames
import MhfeLean.Chapters.DeniabilityRecords
import MhfeLean.Chapters.WalletPairAttack
import MhfeLean.Chapters.SelectionRules
import MhfeLean.Chapters.PasswordDomains
import MhfeLean.Chapters.PassphraseDomains
import MhfeLean.Chapters.TrialCount

/-! # Common proof inventory

The root imports the mathematical chapters and requests one transitive axiom
report. Read README.md here for source statements, model scope and entry points.
-/

open Lean

namespace ProofInventory

/-- All local declarations, including private helpers and unused definitions. -/
def isLocal (name : Name) : Bool :=
  name.toString.startsWith "MhfeLean." || name.toString.startsWith "_private.MhfeLean."

/-- One shared dependency traversal checks the complete development. -/
def report : CoreM Unit := do
  let env ← getEnv
  let roots := env.constants.fold (init := #[]) fun roots name _ =>
    if isLocal name then roots.push name else roots
  unless !roots.isEmpty do
    throwError "No MHFE declarations were checked"
  for name in roots do
    unless (env.checked.get.find? name).isSome do
      throwError "Unchecked declaration: {name}"
  let ownAxioms := roots.filter fun name => match env.find? name with
    | some (.axiomInfo _) => true
    | _ => false
  unless ownAxioms.isEmpty do
    throwError "Local axioms are forbidden: {ownAxioms}"
  -- Port to Lean 4.35: the traversal `CollectAxioms.collect` became private; the public
  -- `collectAxioms` gives the same transitive axioms of each root, joined here into one set.
  let mut collectedSet : NameSet := {}
  for name in roots do
    for axiomName in (← collectAxioms name) do
      collectedSet := collectedSet.insert axiomName
  let collectedAxioms := collectedSet.toArray.qsort Name.lt
  let unexpected := collectedAxioms.filter fun name =>
    name != `propext && name != `Classical.choice && name != `Quot.sound
  unless unexpected.isEmpty do
    throwError "Unexpected proof axioms: {unexpected}"
  let theoremCount := roots.filter fun name => match env.find? name with
    | some (.thmInfo _) => true
    | _ => false
  let inventory := Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("roots", toJson (roots.map Name.toString)),
    ("theorems", toJson theoremCount.size),
    ("axioms", toJson (collectedAxioms.map Name.toString)),
    ("local_axioms", toJson (ownAxioms.map Name.toString))]
  -- Written to the working directory of the build.
  IO.FS.writeFile "checkpoint-inventory.json" inventory.compress
  logInfo m!"MHFE_COMPLETE_AXIOM_INVENTORY|{roots.size}|{theoremCount.size}|standard"

end ProofInventory

#eval ProofInventory.report
