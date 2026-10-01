import Tablet.BaseMultiSequence
import Tablet.BaseShift

-- [TABLET NODE: BasePerfect]
def BasePerfect {Q : Type} (r : Q → Q → Prop) {X : Set Nat}
    (h : BaseMultiSequence X Q) : Prop :=
-- BODY
  ∀ x, r (h x) (h (BaseShift X x))
