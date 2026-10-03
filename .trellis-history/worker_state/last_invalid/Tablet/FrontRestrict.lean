import Tablet.Preamble

-- [TABLET NODE: FrontRestrict]
def FrontRestrict (F : Set (Finset Nat)) (Y : Set Nat) : Set (Finset Nat) :=
-- BODY
  {s | s ∈ F ∧ ∀ n, n ∈ s → n ∈ Y}
