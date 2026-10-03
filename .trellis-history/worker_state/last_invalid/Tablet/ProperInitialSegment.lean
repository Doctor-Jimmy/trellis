import Tablet.InitialSegment

-- [TABLET NODE: ProperInitialSegment]
def ProperInitialSegment (u v : Finset Nat) : Prop :=
-- BODY
  InitialSegment u v ∧ u ≠ v
