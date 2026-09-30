import Tablet.IncSeqId
import Tablet.IncSeqPointwiseLe

-- [TABLET NODE: FirstMovedPoint]
theorem FirstMovedPoint (g : IncSeq) (hg : g ≠ IncSeqId) :
    ∃ k : Nat, k < g k ∧ ∀ j < k, g j = j := by
-- BODY
  sorry
