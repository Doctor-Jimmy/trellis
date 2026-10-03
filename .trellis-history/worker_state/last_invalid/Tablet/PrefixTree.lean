import Tablet.InitialSegment

-- [TABLET NODE: PrefixTree]
def PrefixTree (F : Set (Finset Nat)) : Set (Finset Nat) :=
-- BODY
  {s | ∃ t ∈ F, InitialSegment s t}
