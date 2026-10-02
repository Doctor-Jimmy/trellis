import Tablet.LocallyConstant
import Tablet.MultiSequenceRestrict

-- [TABLET NODE: RestrictionLocallyConstant]
theorem RestrictionLocallyConstant {E : Type} (h : MultiSequence E)
    (z : IncSeq) : LocallyConstant h →
      LocallyConstant (MultiSequenceRestrict h z) := by
-- BODY
  intro hlc x
  obtain ⟨m, hm⟩ := hlc (IncSeqComp z x)
  refine ⟨m, ?_⟩
  intro y hy
  change h (IncSeqComp z y) = h (IncSeqComp z x)
  apply hm
  intro i hi
  change z (x i) = z (y i)
  exact congrArg z (hy i hi)
