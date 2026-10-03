import Tablet.PowerCopiedLeft
import Tablet.PowerShiftIterShift

universe u

-- [TABLET NODE: PowerCopiedShiftIdentity]
theorem PowerCopiedShiftIdentity {Q : Type u} (r : Q → Q → Prop)
    (h : MultiSequence (PowerQ Q)) (x : IncSeq) (n k : Nat) :
    PowerCopiedLeft r h (ShiftMap x) n k =
      PowerCopiedLeft r h x (n + 1) k := by
-- BODY
  induction k generalizing n with
  | zero =>
      simp only [PowerCopiedLeft, PowerCopiedLeft.go.eq_1]
      rw [PowerShiftIterShift n x, PowerShiftIterShift (n + 1) x]
  | succ k ih =>
      change PowerIResponse r
          (PowerCopiedLeft r h (ShiftMap x) n k)
          (PowerCopiedLeft r h (ShiftMap x) (n + 1) k) =
        PowerIResponse r
          (PowerCopiedLeft r h x (n + 1) k)
          (PowerCopiedLeft r h x ((n + 1) + 1) k)
      rw [ih n, ih (n + 1)]
