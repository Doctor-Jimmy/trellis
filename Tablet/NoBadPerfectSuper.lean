import Tablet.BadSuperSequence
import Tablet.BaseShift
import Tablet.FrontPrefixExists
import Tablet.PerfectSuperSequence
import Tablet.InfiniteSetEnumeration

-- [TABLET NODE: NoBadPerfectSuper]
theorem NoBadPerfectSuper {Q : Type} (r : Q → Q → Prop)
    {F : Set (Finset Nat)} {X : Set Nat} (f : SuperSequence F X Q) :
    PerfectSuperSequence r f → BadSuperSequence r f → False := by
-- BODY
  sorry
