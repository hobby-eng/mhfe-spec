import MhfeLean

namespace MhfeLean
theorem AuditNative : (2 : Nat) + 2 = 4 := by native_decide
end MhfeLean

#eval ProofInventory.report
