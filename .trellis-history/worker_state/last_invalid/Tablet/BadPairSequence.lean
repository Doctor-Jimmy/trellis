import Tablet.IncreasingPair

-- [TABLET NODE: BadPairSequence]
def BadPairSequence {Q : Type} (r : Q → Q → Prop)
    (f : IncreasingPair → Q) : Prop :=
-- BODY
  ∀ (m n l : Nat) (hmn : m < n) (hnl : n < l),
    ¬ r (f ⟨m, n, hmn⟩) (f ⟨n, l, hnl⟩)

