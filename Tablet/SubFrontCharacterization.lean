import Tablet.Front
import Tablet.FrontRestrict
import Tablet.FrontRestriction

-- [TABLET NODE: SubFrontCharacterization]
theorem SubFrontCharacterization (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (F' : Set (Finset Nat))
    (hsub : F' ⊆ F) :
    (∃ Y : Set Nat, Front F' Y) ↔
      ∃ Z : Set Nat, Z ⊆ X ∧ Z.Infinite ∧ F' = FrontRestrict F Z := by
-- BODY
  sorry
