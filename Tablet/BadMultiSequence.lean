import Tablet.LocallyConstant
import Tablet.ShiftMap

-- [TABLET NODE: BadMultiSequence]
def BadMultiSequence {Q : Type} (r : Q → Q → Prop) (h : MultiSequence Q) : Prop :=
-- BODY
  ∀ x, ¬ r (h x) (h (ShiftMap x))
