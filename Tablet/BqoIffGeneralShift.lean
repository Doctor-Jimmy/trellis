import Tablet.GBetterRelIff
import Tablet.GBetterRel
import Tablet.Bqo
import Tablet.BadMultiSequence
import Tablet.ShiftMap
import Tablet.IncSeqId
import Tablet.RightComp
import Tablet.SuccSeq

-- [TABLET NODE: BqoIffGeneralShift]
theorem BqoIffGeneralShift {Q : Type} (r : Q → Q → Prop)
    (hpre : IsPreorder Q r) :
    Bqo r ↔
      ∀ (phi : IncSeq → Q), LocallyConstant phi →
        ∀ g : IncSeq, ∃ f : IncSeq,
          r (phi f) (phi (RightComp g f)) := by
-- BODY
  sorry
