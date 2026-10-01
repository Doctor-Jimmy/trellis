import Tablet.BaseMultiSequence
import Tablet.BaseRightComp

-- [TABLET NODE: BaseRestrict]
def BaseRestrict {X : Set Nat} {E : Type} (h : BaseMultiSequence X E) (z : IncSeq) :
    BaseMultiSequence X E :=
-- BODY
  fun x => h (BaseRightComp X z x)
