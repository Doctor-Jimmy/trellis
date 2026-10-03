import Tablet.IncSeq

-- [TABLET NODE: IncSeqId]
def IncSeqId : IncSeq :=
-- BODY
  OrderEmbedding.ofStrictMono id strictMono_id
