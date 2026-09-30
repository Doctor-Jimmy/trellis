import Tablet.Front
import Tablet.FrontRestrict
import Tablet.FrontRestriction

-- [TABLET NODE: SubFrontCharacterization]
theorem SubFrontCharacterization (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (F' : Set (Finset Nat)) (Y : Set Nat)
    (hsub : F' ⊆ F) :
    Front F' Y ↔
      ∃ Z : Set Nat, Z ⊆ X ∧ Z.Infinite ∧ F' = FrontRestrict F Z := by
-- BODY
  sorry
