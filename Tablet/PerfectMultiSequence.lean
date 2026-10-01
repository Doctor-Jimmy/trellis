import Tablet.MultiSequence
import Tablet.ShiftMap

-- [TABLET NODE: PerfectMultiSequence]
def PerfectMultiSequence {Q : Type} (r : Q → Q → Prop)
    (h : MultiSequence Q) : Prop :=
-- BODY
  ∀ x, r (h x) (h (ShiftMap x))
