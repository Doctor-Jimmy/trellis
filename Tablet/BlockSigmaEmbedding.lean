import Tablet.BlockSigma
import Tablet.OrbitBlockCoverage
import Tablet.IncSeq

-- [TABLET NODE: BlockSigmaEmbedding]
theorem BlockSigmaEmbedding (g : IncSeq) (k : Nat) (hk : k < g k) (f : IncSeq) :
    ∃ σ : IncSeq, ∀ l, σ l = BlockSigma g k f l := by
-- BODY
  sorry
