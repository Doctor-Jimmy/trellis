import Tablet.Front
import Tablet.FrontRestrict

-- [TABLET NODE: FrontRestriction]
theorem FrontRestriction (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (Y : Set Nat) (hY : Y ⊆ X) (hYinf : Y.Infinite) :
    Front (FrontRestrict F Y) Y := by
-- BODY
  sorry
