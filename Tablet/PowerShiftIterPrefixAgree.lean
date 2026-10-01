import Tablet.PowerShiftIter
import Tablet.PrefixAgree

universe u

-- [TABLET NODE: PowerShiftIterPrefixAgree]
theorem PowerShiftIterPrefixAgree (x y : IncSeq) (j n : Nat)
    (hxy : PrefixAgree (n + j) x y) :
    PrefixAgree n (PowerShiftIter j x) (PowerShiftIter j y) := by
-- BODY
  sorry
