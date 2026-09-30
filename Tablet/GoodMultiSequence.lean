import Tablet.LocallyConstant
import Tablet.ShiftMap

-- [TABLET NODE: GoodMultiSequence]
def GoodMultiSequence {Q : Type} (r : Q → Q → Prop) (h : MultiSequence Q) : Prop :=
-- BODY
  ∃ x, r (h x) (h (ShiftMap x))
