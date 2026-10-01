import Tablet.BadMultiSequence
import Tablet.BadMultiToSuper
import Tablet.DecidingFront
import Tablet.DecidingFrontSet
import Tablet.DecidingValue
import Tablet.IncSeqId
import Tablet.ShiftMap

universe u

-- [TABLET NODE: BadMultiToNontrivialSuper]
theorem BadMultiToNontrivialSuper {Q : Type u} (r : Q → Q → Prop)
    [Std.Refl r] (h : MultiSequence Q) (hlc : LocallyConstant h)
    (hbad : BadMultiSequence r h) :
    ∃ f : SuperSequence (DecidingFrontSet h) Set.univ Q,
      BadSuperSequence r f ∧ ∅ ∉ DecidingFrontSet h := by
-- BODY
  sorry
