import Tablet.BlockSigma
import Tablet.OrbitBlockCoverage
import Tablet.PrefixAgree

-- [TABLET NODE: BlockSigmaContinuous]
theorem BlockSigmaContinuous (g : IncSeq) (k : Nat) (hk : k < g k) :
    ∀ f : IncSeq, ∀ n : Nat, ∃ m : Nat, ∀ h : IncSeq,
      PrefixAgree m f h → ∀ l < n, BlockSigma g k h l = BlockSigma g k f l := by
-- BODY
  sorry
