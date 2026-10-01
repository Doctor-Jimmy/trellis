import Tablet.Bqo
import Tablet.BaseLocallyConstant
import Tablet.BasePerfect
import Tablet.BaseRestrict
import Tablet.ShiftDichotomy
import Tablet.InfiniteSetEnumeration

-- [TABLET NODE: BaseBqoRestriction]
theorem BaseBqoRestriction {Q : Type} (r : Q → Q → Prop)
    [IsPreorder Q r] (hb : Bqo r) (X : Set Nat) (hX : X.Infinite)
    (h : BaseMultiSequence X Q) (hlc : BaseLocallyConstant h) :
    ∃ z : IncSeq, BasePerfect r (BaseRestrict h z) := by
-- BODY
  sorry
