import Tablet.FrontBridge
import Tablet.FrontTreeSingleton
import Tablet.FrontTreeOrderedExtension

-- [TABLET NODE: FrontBridgeInit]
theorem FrontBridgeInit (F : Set (Finset Nat))
    (hF : Front F Set.univ) (htriv : ∅ ∉ F) {m n : Nat} (hmn : m < n) :
    FrontBridge F ({m} : Finset Nat) ({n} : Finset Nat)
      ({m, n} : Finset Nat) := by
-- BODY
  sorry
