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
  intro n k
  induction k generalizing n with
  | zero =>
      have hraw : ¬ PowerRel r (h (PowerShiftIter n x))
          (h (PowerShiftIter (n + 1) x)) := by
        simpa [PowerShiftIter] using hbad (PowerShiftIter n x)
      have hrawNext : ¬ PowerRel r (h (PowerShiftIter (n + 1) x))
          (h (PowerShiftIter (n + 2) x)) := by
        simpa [PowerShiftIter] using hbad (PowerShiftIter (n + 1) x)
      have hmoveNext : PowerMove (h (PowerShiftIter (n + 1) x))
          (PowerIResponse r (h (PowerShiftIter (n + 1) x))
            (h (PowerShiftIter (n + 2) x))) :=
        PowerIResponseLegal r hrawNext
      have hfail : ¬ PowerRel r
          (PowerIResponse r (h (PowerShiftIter n x))
            (h (PowerShiftIter (n + 1) x)))
            (PowerIResponse r (h (PowerShiftIter (n + 1) x))
              (h (PowerShiftIter (n + 2) x))) :=
        PowerIResponseFailure r hraw hmoveNext
      have hmove : PowerMove
          (PowerIResponse r (h (PowerShiftIter n x))
            (h (PowerShiftIter (n + 1) x)))
          (PowerIResponse r
            (PowerIResponse r (h (PowerShiftIter n x))
              (h (PowerShiftIter (n + 1) x)))
            (PowerIResponse r (h (PowerShiftIter (n + 1) x))
              (h (PowerShiftIter (n + 2) x)))) :=
        PowerIResponseLegal r hfail
      have hleft0 : PowerCopiedLeft r h x n 0 =
          PowerIResponse r (h (PowerShiftIter n x))
            (h (PowerShiftIter (n + 1) x)) := by
        rfl
      have hleft0Next : PowerCopiedLeft r h x (n + 1) 0 =
          PowerIResponse r (h (PowerShiftIter (n + 1) x))
            (h (PowerShiftIter (n + 2) x)) := by
        rfl
      have hleft1 : PowerCopiedLeft r h x n 1 =
          PowerIResponse r
            (PowerIResponse r (h (PowerShiftIter n x))
              (h (PowerShiftIter (n + 1) x)))
            (PowerIResponse r (h (PowerShiftIter (n + 1) x))
              (h (PowerShiftIter (n + 2) x))) := by
        rfl
      constructor
      · rw [hleft0, hleft0Next]
        exact hfail
      · rw [hleft0, hleft1]
        exact hmove
  | succ k ih =>
      have hfail := (ih n).1
      have hmoveNext := (ih (n + 1)).2
      have hfailNext : ¬ PowerRel r
          (PowerIResponse r (PowerCopiedLeft r h x n k)
            (PowerCopiedLeft r h x (n + 1) k))
          (PowerCopiedLeft r h x (n + 1) (k + 1)) :=
        PowerIResponseFailure r hfail hmoveNext
      have hmove : PowerMove
          (PowerIResponse r (PowerCopiedLeft r h x n k)
            (PowerCopiedLeft r h x (n + 1) k))
          (PowerIResponse r
            (PowerIResponse r (PowerCopiedLeft r h x n k)
              (PowerCopiedLeft r h x (n + 1) k))
            (PowerCopiedLeft r h x (n + 1) (k + 1))) :=
        PowerIResponseLegal r hfailNext
      have hleftSucc : PowerCopiedLeft r h x n (k + 1) =
          PowerIResponse r (PowerCopiedLeft r h x n k)
            (PowerCopiedLeft r h x (n + 1) k) := by
        rfl
      have hleftSuccNext : PowerCopiedLeft r h x (n + 1) (k + 1) =
          PowerIResponse r (PowerCopiedLeft r h x (n + 1) k)
            (PowerCopiedLeft r h x (n + 2) k) := by
        rfl
      have hleftNextSucc : PowerCopiedLeft r h x n (k + 1 + 1) =
          PowerIResponse r (PowerCopiedLeft r h x n (k + 1))
            (PowerCopiedLeft r h x (n + 1) (k + 1)) := by
        rfl
      constructor
      · rw [hleftSucc, hleftSuccNext]
        exact hfailNext
      · rw [hleftSucc, hleftNextSucc]
        exact hmove
