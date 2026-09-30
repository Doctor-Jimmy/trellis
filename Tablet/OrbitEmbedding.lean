import Tablet.OrbitPoint
import Tablet.IncSeq

-- [TABLET NODE: OrbitEmbedding]
theorem OrbitEmbedding (g : IncSeq) (k : Nat) (hk : k < g k) :
    ∃ G : IncSeq, ∀ n, G n = OrbitPoint g k n := by
-- BODY
  sorry
