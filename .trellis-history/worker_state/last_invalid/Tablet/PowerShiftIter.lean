import Tablet.ShiftMap

-- [TABLET NODE: PowerShiftIter]
def PowerShiftIter : Nat → IncSeq → IncSeq :=
-- BODY
  fun n x => Nat.rec x (fun _ z => ShiftMap z) n
