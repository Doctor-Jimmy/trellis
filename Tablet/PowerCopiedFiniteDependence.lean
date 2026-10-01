import Tablet.PowerCopiedLeft

universe u

-- [TABLET NODE: PowerCopiedFiniteDependence]
theorem PowerCopiedFiniteDependence {Q : Type u} (r : Q → Q → Prop)
    (h h' : MultiSequence (PowerQ Q)) (x : IncSeq) (n k : Nat)
    (hag : ∀ j : Nat, j ≤ n + k + 2 →
      h' (PowerShiftIter j x) = h (PowerShiftIter j x)) :
    PowerCopiedLeft r h' x n k = PowerCopiedLeft r h x n k := by
-- BODY
  sorry
