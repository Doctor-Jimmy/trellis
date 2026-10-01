import Tablet.IncSeq

-- [TABLET NODE: InfiniteSetEnumeration]
theorem InfiniteSetEnumeration (X : Set Nat) (hX : X.Infinite) :
    ∃ x : IncSeq, Set.range (x : Nat → Nat) = X := by
-- BODY
  sorry
