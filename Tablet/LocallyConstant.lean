import Tablet.MultiSequence
import Tablet.PrefixAgree

-- [TABLET NODE: LocallyConstant]
def LocallyConstant {E : Type} (h : MultiSequence E) : Prop :=
-- BODY
  ∀ x, ∃ n, ∀ y, PrefixAgree n x y → h y = h x
