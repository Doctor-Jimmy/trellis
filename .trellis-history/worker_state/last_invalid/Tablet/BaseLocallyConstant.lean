import Tablet.BaseMultiSequence
import Tablet.PrefixAgree

-- [TABLET NODE: BaseLocallyConstant]
def BaseLocallyConstant {X : Set Nat} {E : Type} (h : BaseMultiSequence X E) : Prop :=
-- BODY
  ∀ x, ∃ n, ∀ y, PrefixAgree n x.1 y.1 → h y = h x
