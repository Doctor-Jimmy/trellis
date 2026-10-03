import Tablet.PowerCopiedLeft

universe u

-- [TABLET NODE: PowerCopiedOrbitDependence]
theorem PowerCopiedOrbitDependence {Q : Type u} (r : Q → Q → Prop)
    (h : MultiSequence (PowerQ Q)) (x y : IncSeq) (n k : Nat)
    (hag : ∀ j : Nat, j ≤ n + k + 2 →
      h (PowerShiftIter j x) = h (PowerShiftIter j y)) :
    PowerCopiedLeft r h x n k = PowerCopiedLeft r h y n k := by
-- BODY
  have stronger : ∀ (m i : Nat),
      (∀ j : Nat, j ≤ i + m + 2 →
        h (PowerShiftIter j x) = h (PowerShiftIter j y)) →
      PowerCopiedLeft r h x i m = PowerCopiedLeft r h y i m := by
    intro m
    induction m with
    | zero =>
        intro i hi
        change PowerIResponse r (h (PowerShiftIter i x))
            (h (PowerShiftIter (i + 1) x)) =
          PowerIResponse r (h (PowerShiftIter i y))
            (h (PowerShiftIter (i + 1) y))
        rw [hi i (by omega), hi (i + 1) (by omega)]
    | succ m ih =>
        intro i hi
        change PowerIResponse r
            (PowerCopiedLeft r h x i m)
            (PowerCopiedLeft r h x (i + 1) m) =
          PowerIResponse r
            (PowerCopiedLeft r h y i m)
            (PowerCopiedLeft r h y (i + 1) m)
        rw [ih i (by
          intro j hj
          exact hi j (by omega)),
          ih (i + 1) (by
            intro j hj
            exact hi j (by omega))]
  exact stronger k n hag
