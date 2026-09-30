import Tablet.BlockSigma
import Tablet.OrbitBlockCoverage
import Tablet.RightComp
import Tablet.SuccSeq

-- [TABLET NODE: BlockSigmaIntertwines]
theorem BlockSigmaIntertwines (g : IncSeq) (k : Nat) (hk : k < g k) :
    ∀ f : IncSeq, ∀ l : Nat,
      BlockSigma g k (RightComp SuccSeq f) l = BlockSigma g k f (g l) := by
-- BODY
  sorry
