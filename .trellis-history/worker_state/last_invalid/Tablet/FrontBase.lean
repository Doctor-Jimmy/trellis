import Tablet.Preamble

-- [TABLET NODE: FrontBase]
def FrontBase (F : Set (Finset Nat)) : Set Nat :=
-- BODY
  {n | ∃ s, s ∈ F ∧ n ∈ s}
