import Tablet.PowerShiftIter

-- [TABLET NODE: PowerShiftIterShift]
theorem PowerShiftIterShift (n : Nat) (x : IncSeq) :
    PowerShiftIter n (ShiftMap x) = PowerShiftIter (n + 1) x := by
-- BODY
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      change ShiftMap (PowerShiftIter n (ShiftMap x)) =
        ShiftMap (PowerShiftIter (n + 1) x)
      exact congrArg ShiftMap (ih x)
