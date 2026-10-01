import Tablet.IncSeqComp
import Tablet.MultiSequenceRestrict
import Tablet.ShiftMap

-- [TABLET NODE: RestrictionShift]
theorem RestrictionShift {E : Type} (h : MultiSequence E) (z : IncSeq) :
    ∀ x : IncSeq,
      MultiSequenceRestrict h z (ShiftMap x) =
        MultiSequenceRestrict h (IncSeqComp SuccSeq z) x := by
-- BODY
  sorry
