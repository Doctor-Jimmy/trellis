import Tablet.BaseMultiSequence
import Tablet.BaseShift

-- [TABLET NODE: BaseBad]
def BaseBad {Q : Type} (r : Q → Q → Prop) {X : Set Nat}
    (h : BaseMultiSequence X Q) : Prop :=
-- BODY
  ∀ x, ¬ r (h x) (h (BaseShift X x))
