import Tablet.LocallyConstant
import Tablet.MultiSequenceRestrict

-- [TABLET NODE: RestrictionLocallyConstant]
theorem RestrictionLocallyConstant {E : Type} (h : MultiSequence E)
    (z : IncSeq) : LocallyConstant h →
      LocallyConstant (MultiSequenceRestrict h z) := by
-- BODY
  sorry
