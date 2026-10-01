import Tablet.MultiSequence
import Tablet.PrefixAgree

universe u

-- [TABLET NODE: LocallyConstant]
def LocallyConstant {E : Type u} (h : MultiSequence E) : Prop :=
-- BODY
  ∀ x, ∃ n, ∀ y, PrefixAgree n x y → h y = h x
