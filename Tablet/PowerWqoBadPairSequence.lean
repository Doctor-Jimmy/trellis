import Tablet.BadPairSequence
import Tablet.SetDomination

-- [TABLET NODE: PowerWqoBadPairSequence]
theorem PowerWqoBadPairSequence {Q : Type} (r : Q → Q → Prop)
    [IsPreorder Q r] :
    ¬ WellQuasiOrdered (SetDomination r) ↔
      ∃ f : IncreasingPair → Q, BadPairSequence r f := by
-- BODY
  sorry

