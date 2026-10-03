import Tablet.LocallyConstant
import Tablet.ProperInitialSegment
import Tablet.ProperPrefixSet

universe u

-- [TABLET NODE: DecidingPrefix]
def DecidingPrefix {E : Type u} (h : MultiSequence E) (s : Finset Nat) : Prop :=
-- BODY
  ∀ x y : IncSeq, ProperPrefixSet s (Set.range (x : Nat → Nat)) →
    ProperPrefixSet s (Set.range (y : Nat → Nat)) → h x = h y
