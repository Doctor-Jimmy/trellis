import Tablet.IncreasingPair

-- [TABLET NODE: RadoOrder]
def RadoOrder (p q : IncreasingPair) : Prop :=
-- BODY
  (p.first = q.first ∧ p.second ≤ q.second) ∨ p.second < q.first

