import Tablet.ProperPrefixSet
import Tablet.ShiftMap

-- [TABLET NODE: FiniteShift]
def FiniteShift (s t : Finset Nat) : Prop :=
-- BODY
  ∃ x : IncSeq, ProperPrefixSet s (Set.range (x : Nat → Nat)) ∧
    ProperPrefixSet t (Set.range (ShiftMap x : Nat → Nat))
