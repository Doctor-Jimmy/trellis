import Tablet.BadMultiSequence
import Tablet.MultiSequenceRestrict
import Tablet.RestrictionShift

-- [TABLET NODE: BadMultiRestrict]
theorem BadMultiRestrict {Q : Type} (r : Q → Q → Prop)
    (h : MultiSequence Q) (z : IncSeq) :
    BadMultiSequence r h →
      BadMultiSequence r (MultiSequenceRestrict h z) := by
-- BODY
  sorry
