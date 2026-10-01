import Tablet.MultiSequence
import Tablet.RightComp

-- [TABLET NODE: MultiSequenceRestrict]
def MultiSequenceRestrict {E : Type} (h : MultiSequence E) (z : IncSeq) :
    MultiSequence E :=
-- BODY
  fun x => h (RightComp z x)
