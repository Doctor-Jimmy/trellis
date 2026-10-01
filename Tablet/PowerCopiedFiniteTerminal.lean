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
  sorry
