import Tablet.IncSeq

-- [TABLET NODE: IncSeqComp]
def IncSeqComp (f g : IncSeq) : IncSeq :=
-- BODY
  g.comp f
