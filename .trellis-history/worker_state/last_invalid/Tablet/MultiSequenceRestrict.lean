import Tablet.MultiSequence
import Tablet.IncSeqComp

-- [TABLET NODE: MultiSequenceRestrict]
def MultiSequenceRestrict {E : Type} (h : MultiSequence E) (z : IncSeq) :
    MultiSequence E :=
-- BODY
  fun x => h (IncSeqComp z x)
