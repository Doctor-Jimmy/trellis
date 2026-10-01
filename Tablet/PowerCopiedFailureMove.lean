import Tablet.PowerCopiedLeft
import Tablet.PowerIResponseFailure
import Tablet.PowerIResponseLegal
import Tablet.BadMultiSequence

universe u

-- [TABLET NODE: PowerCopiedFailureMove]
theorem PowerCopiedFailureMove {Q : Type u} (r : Q → Q → Prop)
    (h : MultiSequence (PowerQ Q))
    (hbad : BadMultiSequence (PowerRel r) h) (x : IncSeq) :
    ∀ n k,
      (¬ PowerRel r (PowerCopiedLeft r h x n k)
          (PowerCopiedLeft r h x (n + 1) k)) ∧
        PowerMove (PowerCopiedLeft r h x n k)
          (PowerCopiedLeft r h x n (k + 1)) := by
-- BODY
  sorry
