import Tablet.LocallyConstant
import Tablet.ShiftMap

universe u

-- [TABLET NODE: BadMultiSequence]
def BadMultiSequence {Q : Type u} (r : Q → Q → Prop) (h : MultiSequence Q) : Prop :=
-- BODY
  ∀ x, ¬ r (h x) (h (ShiftMap x))
