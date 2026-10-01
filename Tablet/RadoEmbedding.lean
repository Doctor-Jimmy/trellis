import Tablet.PowerWqoBadPairSequence
import Tablet.TripleHomogeneous
import Tablet.QuadrupleHomogeneous
import Tablet.InfiniteSetEnumeration
import Tablet.RadoOrder
import Tablet.RelationEmbedding

-- [TABLET NODE: RadoEmbedding]
theorem RadoEmbedding {Q : Type} (r : Q → Q → Prop) [IsPreorder Q r]
    (hQ : WellQuasiOrdered r)
    (hP : ¬ WellQuasiOrdered (SetDomination r)) :
    ∃ e : IncreasingPair → Q, RelationEmbedding RadoOrder r e := by
-- BODY
  sorry
