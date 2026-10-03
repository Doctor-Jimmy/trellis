import Tablet.ContMor
import Tablet.RightComp
import Tablet.ShiftMap
import Tablet.FirstMovedPoint
import Tablet.BlockSigmaEmbedding
import Tablet.BlockSigmaContinuous
import Tablet.BlockSigmaIntertwines

-- [TABLET NODE: EmapLemma]
theorem EmapLemma (g : IncSeq) (hg : g ≠ IncSeqId) :
    ContMor ShiftMap (RightComp g) := by
-- BODY
  classical
  obtain ⟨k, hk, hfix⟩ := FirstMovedPoint g hg
  let sigma : IncSeq → IncSeq := fun f =>
    Classical.choose (BlockSigmaEmbedding g k hk f)
  have hsigma : ∀ f l, sigma f l = BlockSigma g k f l := by
    intro f l
    simpa [sigma] using (Classical.choose_spec (BlockSigmaEmbedding g k hk f) l)
  have hcontinuous : BaireContinuous sigma := by
    intro f n
    obtain ⟨m, hm⟩ := BlockSigmaContinuous g k hk f n
    refine ⟨m, ?_⟩
    intro h hfh l hl
    rw [hsigma f l, hsigma h l]
    exact (hm h hfh l hl).symm
  have hcommutes : ∀ f, sigma (ShiftMap f) = RightComp g (sigma f) := by
    intro f
    apply DFunLike.ext (sigma (ShiftMap f)) (RightComp g (sigma f))
    intro l
    calc
      sigma (ShiftMap f) l = BlockSigma g k (ShiftMap f) l := hsigma _ _
      _ = BlockSigma g k f (g l) := by
        simpa [ShiftMap, RightComp, IncSeqComp] using
          (BlockSigmaIntertwines g k hk hfix f l)
      _ = (RightComp g (sigma f)) l := by
        change BlockSigma g k f (g l) = sigma f (g l)
        exact (hsigma f (g l)).symm
  refine ⟨⟨sigma, hcontinuous, hcommutes⟩⟩
