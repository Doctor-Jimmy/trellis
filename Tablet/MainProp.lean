import Tablet.ContMorEq
import Tablet.RmapLemma
import Tablet.EmapLemma

-- [TABLET NODE: MainProp]
theorem MainProp (g : IncSeq) (hg : g ≠ IncSeqId) :
    ContMorEq (RightComp g) ShiftMap := by
-- BODY
  unfold ContMorEq
  exact ⟨RmapLemma g hg, EmapLemma g hg⟩
