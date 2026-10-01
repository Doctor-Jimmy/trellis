import Tablet.PowerCopiedLeft

universe u

-- [TABLET NODE: PowerCopiedOrbitDependence]
theorem PowerCopiedOrbitDependence {Q : Type u} (r : Q → Q → Prop)
    (h : MultiSequence (PowerQ Q)) (x y : IncSeq) (n k : Nat)
    (hag : ∀ j : Nat, j ≤ n + k + 2 →
      h (PowerShiftIter j x) = h (PowerShiftIter j y)) :
    PowerCopiedLeft r h x n k = PowerCopiedLeft r h y n k := by
-- BODY
  sorry
