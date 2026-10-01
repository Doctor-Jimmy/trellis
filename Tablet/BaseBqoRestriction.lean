import Tablet.Bqo
import Tablet.BaseLocallyConstant
import Tablet.BaseRestrict
import Tablet.PerfectMultiSequence
import Tablet.ShiftDichotomy
import Tablet.InfiniteSetEnumeration

-- [TABLET NODE: BaseBqoRestriction]
theorem BaseBqoRestriction {Q : Type} (r : Q → Q → Prop)
    [IsPreorder Q r] (hb : Bqo r) (X : Set Nat) (hX : X.Infinite)
    (h : BaseMultiSequence X Q) (hlc : BaseLocallyConstant h) :
    ∃ z : BaseIncSeq X, PerfectMultiSequence r (BaseRestrict h z) := by
-- BODY
  sorry
