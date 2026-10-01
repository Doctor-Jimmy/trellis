import Tablet.PowerCopiedFailureMove
import Tablet.PowerMoveInSupport

universe u

-- [TABLET NODE: PowerCopiedSupport]
theorem PowerCopiedSupport {Q : Type u} (r : Q → Q → Prop)
    (h : MultiSequence (PowerQ Q))
    (hbad : BadMultiSequence (PowerRel r) h) (x : IncSeq) :
    ∀ n k,
      PowerSupport (PowerCopiedLeft r h x n k) ⊆
        PowerSupport (h (PowerShiftIter n x)) := by
-- BODY
  sorry
