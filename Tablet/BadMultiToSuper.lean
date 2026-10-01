import Tablet.BadMultiSequence
import Tablet.BadSuperSequence
import Tablet.DecidingPrefix
import Tablet.DecidingFrontSet
import Tablet.DecidingValue

universe u

-- [TABLET NODE: BadMultiToSuper]
theorem BadMultiToSuper {Q : Type u} (r : Q → Q → Prop)
    (h : MultiSequence Q) (f : SuperSequence (DecidingFrontSet h) Set.univ Q)
    (hf : ∀ (s : DecidingFrontSet h) (x : IncSeq),
      ProperPrefixSet s.1 (Set.range (x : Nat → Nat)) → f.value s = h x)
    (hh : BadMultiSequence r h) :
    BadSuperSequence r f := by
-- BODY
  sorry
