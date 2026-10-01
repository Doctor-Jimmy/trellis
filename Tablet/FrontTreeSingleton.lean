import Tablet.Front
import Tablet.PrefixTree

-- [TABLET NODE: FrontTreeSingleton]
theorem FrontTreeSingleton (F : Set (Finset Nat))
    (hF : Front F Set.univ) (htriv : ∅ ∉ F) (n : Nat) :
    ({n} : Finset Nat) ∈ PrefixTree F := by
-- BODY
  sorry
