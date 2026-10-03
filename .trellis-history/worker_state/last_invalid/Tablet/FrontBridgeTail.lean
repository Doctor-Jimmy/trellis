import Tablet.InitialSegment

-- [TABLET NODE: FrontBridgeTail]
def FrontBridgeTail (u : Finset Nat) : Finset Nat :=
-- BODY
  u.filter (fun k => ∃ n ∈ u, n < k)
