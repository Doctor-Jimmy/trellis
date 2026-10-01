import Tablet.Preamble

-- [TABLET NODE: CardinalityFront]
def CardinalityFront (k : Nat) (X : Set Nat) : Set (Finset Nat) :=
-- BODY
  {s | s.card = k ∧ (↑s : Set Nat) ⊆ X}

