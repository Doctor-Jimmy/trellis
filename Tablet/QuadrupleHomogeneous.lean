import Tablet.CardinalityFrontIsFront
import Tablet.NashWilliams

-- [TABLET NODE: QuadrupleHomogeneous]
theorem QuadrupleHomogeneous (X : Set Nat) (hX : X.Infinite)
    (c : Finset Nat → Bool) :
    ∃ Y : Set Nat, Y ⊆ X ∧ Y.Infinite ∧
      ∃ b : Bool, ∀ s : Finset Nat,
        s.card = 4 → (↑s : Set Nat) ⊆ Y → c s = b := by
-- BODY
  sorry

