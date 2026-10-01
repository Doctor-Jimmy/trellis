import Tablet.Front
import Tablet.PrefixTree
import Tablet.ProperInitialSegment

-- [TABLET NODE: FrontTreeWellFounded]
theorem FrontTreeWellFounded (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) :
    WellFounded (fun u v : {s : Finset Nat // s ∈ PrefixTree F} =>
      ProperInitialSegment v.1 u.1) := by
-- BODY
  sorry
