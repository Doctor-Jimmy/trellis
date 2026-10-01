import Tablet.DecidingPrefix
import Tablet.DecidingFrontSet
import Tablet.PerfectMultiSequence
import Tablet.PerfectSuperSequence

-- [TABLET NODE: PerfectMultiToSuper]
theorem PerfectMultiToSuper {Q : Type} (r : Q → Q → Prop)
    (h : MultiSequence Q) (f : SuperSequence (DecidingFrontSet h) Set.univ Q)
    (hf : ∀ (s : DecidingFrontSet h) (x : IncSeq),
      ProperPrefixSet s.1 (Set.range (x : Nat → Nat)) → f.value s = h x)
    (hh : PerfectMultiSequence r h) :
    PerfectSuperSequence r f := by
-- BODY
  sorry
