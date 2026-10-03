import Tablet.PowerShiftIter
import Tablet.PrefixAgree

universe u

-- [TABLET NODE: PowerShiftIterPrefixAgree]
theorem PowerShiftIterPrefixAgree (x y : IncSeq) (j n : Nat)
    (hxy : PrefixAgree (n + j) x y) :
    PrefixAgree n (PowerShiftIter j x) (PowerShiftIter j y) := by
-- BODY
  induction j generalizing n with
  | zero =>
      simpa [PowerShiftIter] using hxy
  | succ j ih =>
      have hxy' : PrefixAgree ((n + 1) + j) x y := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hxy
      have h := ih (n := n + 1) hxy'
      intro i hi
      change PowerShiftIter j x (i + 1) = PowerShiftIter j y (i + 1)
      exact h (i + 1) (Nat.succ_lt_succ hi)
