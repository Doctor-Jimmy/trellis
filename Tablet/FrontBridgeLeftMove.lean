import Tablet.FrontBridge

-- [TABLET NODE: FrontBridgeLeftMove]
theorem FrontBridgeLeftMove (F : Set (Finset Nat))
    {s t u s' : Finset Nat} (hb : FrontBridge F s t u)
    (hchoice : (s ∈ F ∧ s' = s) ∨ (s ∉ F ∧ s' = u)) :
    s' ∈ PrefixTree F ∧
      (s ∈ F → s' = s) ∧
      (s ∉ F → ProperInitialSegment s s') := by
-- BODY
  sorry
