import Tablet.BadMultiSequence
import Tablet.MultiSequenceRestrict
import Tablet.RestrictionShift

-- [TABLET NODE: BadMultiRestrict]
theorem BadMultiRestrict {Q : Type} (r : Q → Q → Prop)
    (h : MultiSequence Q) (z : IncSeq) :
    BadMultiSequence r h →
      BadMultiSequence r (MultiSequenceRestrict h z) := by
-- BODY
  intro hbad x
  have hbad' : ¬ r (h (IncSeqComp z x))
      (h (ShiftMap (IncSeqComp z x))) := hbad (IncSeqComp z x)
  change ¬ r ((MultiSequenceRestrict h z) x)
      ((MultiSequenceRestrict h z) (ShiftMap x))
  rw [show (MultiSequenceRestrict h z) x = h (IncSeqComp z x) by rfl]
  rw [show (MultiSequenceRestrict h z) (ShiftMap x) =
      h (IncSeqComp z (ShiftMap x)) by rfl]
  rw [RestrictionShift]
  exact hbad'
