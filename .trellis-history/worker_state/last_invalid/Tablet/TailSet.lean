import Tablet.Preamble

-- [TABLET NODE: TailSet]
def TailSet (X : Set Nat) (n : Nat) : Set Nat :=
-- BODY
  {k | k ∈ X ∧ n < k}
