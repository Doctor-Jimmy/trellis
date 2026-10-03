import Tablet.PowerCopiedFiniteDependence
import Tablet.PowerCopiedTerminates
import Tablet.PowerCopiedTerminalAt

universe u

-- [TABLET NODE: PowerCopiedFiniteTerminal]
theorem PowerCopiedFiniteTerminal {Q : Type u} (r : Q → Q → Prop)
    (h : MultiSequence (PowerQ Q))
    (hbad : BadMultiSequence (PowerRel r) h) (x : IncSeq) :
    ∃ k q q',
      PowerCopiedLeft r h x 0 k = .atom q ∧
      PowerCopiedLeft r h x 1 k = .atom q' ∧
      ∀ h' : MultiSequence (PowerQ Q),
        (∀ j : Nat, j ≤ k + 2 →
          h' (PowerShiftIter j x) = h (PowerShiftIter j x)) →
        PowerCopiedLeft r h' x 0 k = .atom q := by
-- BODY
  obtain ⟨k, hk⟩ := PowerCopiedTerminates r h hbad x 0
  rcases hk with ⟨q, q', hq, hq'⟩
  refine ⟨k, q, q', hq, hq', ?_⟩
  intro h' hag
  have hcopy := PowerCopiedFiniteDependence r h h' x 0 k (by
    intro j hj
    exact hag j (by omega))
  calc
    PowerCopiedLeft r h' x 0 k = PowerCopiedLeft r h x 0 k := hcopy
    _ = .atom q := hq
