import Tablet.DecidingFront
import Tablet.DecidingValue
import Tablet.BadMultiSequence
import Tablet.MultiSequenceRestrict
import Tablet.NashWilliams
import Tablet.PerfectMultiSequence

-- [TABLET NODE: ShiftDichotomy]
theorem ShiftDichotomy {Q : Type} (r : Q → Q → Prop)
    (h : MultiSequence Q) (hlc : LocallyConstant h) :
    ∃ z : IncSeq,
      PerfectMultiSequence r (MultiSequenceRestrict h z) ∨
        BadMultiSequence r (MultiSequenceRestrict h z) := by
-- BODY
  sorry
