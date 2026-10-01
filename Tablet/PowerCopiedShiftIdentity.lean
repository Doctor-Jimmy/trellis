import Tablet.PowerCopiedLeft
import Tablet.PowerShiftIterShift

universe u

-- [TABLET NODE: PowerCopiedShiftIdentity]
theorem PowerCopiedShiftIdentity {Q : Type u} (r : Q → Q → Prop)
    (h : MultiSequence (PowerQ Q)) (x : IncSeq) (n k : Nat) :
    PowerCopiedLeft r h (ShiftMap x) n k =
      PowerCopiedLeft r h x (n + 1) k := by
-- BODY
  sorry
