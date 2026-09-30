import Tablet.Front
import Tablet.FrontRestrict
import Tablet.FrontRayClosure
import Tablet.FrontRestriction
import Tablet.FrontTreeWellFounded
import Tablet.BooleanInfinitePigeonhole

-- [TABLET NODE: NashWilliams]
theorem NashWilliams (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (S : Set (Finset Nat)) (hS : S ⊆ F) :
    ∃ F' : Set (Finset Nat), ∃ Y : Set Nat,
      Front F' Y ∧ F' ⊆ F ∧ (F' ⊆ S ∨ F' ∩ S = ∅) := by
-- BODY
  sorry
