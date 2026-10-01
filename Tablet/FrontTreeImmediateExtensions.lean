import Tablet.Front
import Tablet.PrefixTree
import Tablet.ProperInitialSegment

-- [TABLET NODE: FrontTreeImmediateExtensions]
theorem FrontTreeImmediateExtensions (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (s : Finset Nat) (hs : s ∈ PrefixTree F)
    (hsF : s ∉ F) :
    Nonempty {n : Nat // n ∉ s ∧ insert n s ∈ PrefixTree F} ∧
      Countable {n : Nat // n ∉ s ∧ insert n s ∈ PrefixTree F} := by
-- BODY
  sorry
