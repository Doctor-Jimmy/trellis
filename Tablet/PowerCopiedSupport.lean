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
  intro n k
  induction k generalizing n with
  | zero =>
      have hraw : ¬ PowerRel r (h (PowerShiftIter n x))
          (h (PowerShiftIter (n + 1) x)) := by
        simpa [PowerShiftIter] using hbad (PowerShiftIter n x)
      have hmove : PowerMove (h (PowerShiftIter n x))
          (PowerCopiedLeft r h x n 0) := by
        change PowerMove (h (PowerShiftIter n x))
          (PowerIResponse r (h (PowerShiftIter n x))
            (h (PowerShiftIter (n + 1) x)))
        exact PowerIResponseLegal r hraw
      exact PowerMoveInSupport hmove
  | succ k ih =>
      have hmove : PowerMove (PowerCopiedLeft r h x n k)
          (PowerCopiedLeft r h x n (k + 1)) :=
        (PowerCopiedFailureMove r h hbad x n k).2
      exact (PowerMoveInSupport hmove).trans (ih n)
