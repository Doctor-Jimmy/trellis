import Tablet.PowerShiftIterPrefixAgree
import Tablet.LocallyConstant

universe u

-- [TABLET NODE: PowerFiniteOrbitConstancy]
theorem PowerFiniteOrbitConstancy {E : Type u} (h : MultiSequence E)
    (hloc : LocallyConstant h) (x : IncSeq) (m : Nat) :
    ∃ N, ∀ y, PrefixAgree N x y →
      ∀ j, j ≤ m →
        h (PowerShiftIter j y) = h (PowerShiftIter j x) := by
-- BODY
  sorry
