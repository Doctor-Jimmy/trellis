import Tablet.DecidingFrontSet
import Tablet.Front

universe u

-- [TABLET NODE: DecidingFront]
theorem DecidingFront {E : Type u} (h : MultiSequence E)
    (hlc : LocallyConstant h) :
    Front (DecidingFrontSet h) Set.univ := by
-- BODY
  sorry
