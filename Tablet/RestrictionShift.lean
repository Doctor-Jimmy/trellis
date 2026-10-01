import Tablet.ShiftMap
import Tablet.MultiSequenceRestrict

-- [TABLET NODE: RestrictionShift]
theorem RestrictionShift (z : IncSeq) :
    ∀ x : IncSeq,
      IncSeqComp z (ShiftMap x) = ShiftMap (IncSeqComp z x) := by
-- BODY
  sorry
