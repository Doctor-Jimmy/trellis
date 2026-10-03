import Tablet.DecidingPrefix
import Tablet.ProperInitialSegment

universe u

-- [TABLET NODE: DecidingFrontSet]
def DecidingFrontSet {E : Type u} (h : MultiSequence E) : Set (Finset Nat) :=
-- BODY
  {s | DecidingPrefix h s ∧
    ∀ t, ProperInitialSegment t s → ¬ DecidingPrefix h t}
