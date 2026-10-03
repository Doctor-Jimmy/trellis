import Tablet.IncSeq

-- [TABLET NODE: OrbitPoint]
def OrbitPoint (g : IncSeq) (k n : Nat) : Nat :=
-- BODY
  (g : Nat → Nat)^[n] k
