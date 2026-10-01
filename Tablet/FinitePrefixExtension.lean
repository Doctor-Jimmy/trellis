import Tablet.IncSeq
import Tablet.ProperPrefixSet

-- [TABLET NODE: FinitePrefixExtension]
theorem FinitePrefixExtension (s : Finset Nat) :
    ∃ x : IncSeq, ProperPrefixSet s (Set.range (x : Nat → Nat)) := by
-- BODY
  sorry
