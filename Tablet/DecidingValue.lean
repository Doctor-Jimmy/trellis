import Tablet.DecidingFront
import Tablet.FinitePrefixExtension

universe u

-- [TABLET NODE: DecidingValue]
theorem DecidingValue {E : Type u} (h : MultiSequence E)
    (hlc : LocallyConstant h) :
    ∃ v : DecidingFrontSet h → E,
      ∀ (s : DecidingFrontSet h) (x : IncSeq),
        ProperPrefixSet s.1 (Set.range (x : Nat → Nat)) → v s = h x := by
-- BODY
  sorry
