import Tablet.FrontBridge
import Tablet.FiniteShift
import Tablet.InfiniteSetEnumeration

-- [TABLET NODE: FrontBridgeTerminal]
theorem FrontBridgeTerminal (F : Set (Finset Nat))
    {s t u : Finset Nat} (hb : FrontBridge F s t u)
    (hs : s ∈ F) (ht : t ∈ F) :
    FiniteShift s t := by
-- BODY
  sorry
