import Tablet.PowerFiniteOrbitConstancy
import Tablet.PowerCopiedOrbitDependence
import Tablet.PowerCopiedTerminalShift
import Tablet.PowerCopiedTerminalSupport
import Tablet.PowerCopiedFailureMove

universe u

-- [TABLET NODE: PowerQReflection]
theorem PowerQReflection {Q : Type u} (r : Q → Q → Prop)
    [IsPreorder Q r] (h : MultiSequence (PowerQ Q))
    (hloc : LocallyConstant h)
    (hbad : BadMultiSequence (PowerRel r) h) :
    ∃ g : MultiSequence Q,
      LocallyConstant g ∧ BadMultiSequence r g ∧
        ∀ x, g x ∈ PowerSupport (h x) := by
-- BODY
  sorry
