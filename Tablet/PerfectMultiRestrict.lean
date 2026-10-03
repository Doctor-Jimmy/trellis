import Tablet.MultiSequenceRestrict
import Tablet.PerfectMultiSequence
import Tablet.RestrictionShift

-- [TABLET NODE: PerfectMultiRestrict]
theorem PerfectMultiRestrict {Q : Type} (r : Q → Q → Prop)
    (h : MultiSequence Q) (z : IncSeq) :
    PerfectMultiSequence r h →
      PerfectMultiSequence r (MultiSequenceRestrict h z) := by
-- BODY
  intro hh x
  change r (h (IncSeqComp z x)) (h (IncSeqComp z (ShiftMap x)))
  rw [RestrictionShift]
  exact hh (IncSeqComp z x)
