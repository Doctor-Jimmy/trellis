import Tablet.FrontBridgeTail
import Tablet.Front
import Tablet.PrefixTree
import Tablet.ProperInitialSegment

-- [TABLET NODE: FrontBridge]
def FrontBridge (F : Set (Finset Nat)) (s t u : Finset Nat) : Prop :=
-- BODY
  s ∈ PrefixTree F ∧
    t ∈ PrefixTree F ∧
    t.Nonempty ∧
    u.Nonempty ∧
    (s ∈ F → InitialSegment s u) ∧
    (s ∉ F → ∃ n, ProperInitialSegment s (insert n s) ∧
      u = insert n s ∧ u ∈ PrefixTree F) ∧
    (t ∈ F → InitialSegment t (FrontBridgeTail u)) ∧
    (t ∉ F → t = FrontBridgeTail u)
