import Tablet.OrbitPoint

-- [TABLET NODE: OrbitBlock]
def OrbitBlock (g : IncSeq) (k n l : Nat) : Prop :=
-- BODY
  OrbitPoint g k n ≤ l ∧ l < OrbitPoint g k (n + 1)
