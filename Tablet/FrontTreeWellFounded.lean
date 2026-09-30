import Tablet.Front
import Tablet.PrefixTree
import Tablet.ProperInitialSegment

-- [TABLET NODE: FrontTreeWellFounded]
theorem FrontTreeWellFounded (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) :
    WellFounded (fun u v : Finset Nat =>
      u ∈ PrefixTree F ∧ v ∈ PrefixTree F ∧ ProperInitialSegment u v) := by
-- BODY
  sorry
