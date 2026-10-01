import Tablet.IncSeq

-- [TABLET NODE: BaseIncSeq]
def BaseIncSeq (X : Set Nat) :=
-- BODY
  {x : IncSeq // Set.range (x : Nat → Nat) ⊆ X}
