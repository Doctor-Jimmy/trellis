import Tablet.PowerCopiedSupport
import Tablet.PowerCopiedTerminates
import Tablet.PowerCopiedTerminalAt

universe u

-- [TABLET NODE: PowerCopiedTerminalSupport]
theorem PowerCopiedTerminalSupport {Q : Type u} (r : Q → Q → Prop)
    (h : MultiSequence (PowerQ Q))
    (hbad : BadMultiSequence (PowerRel r) h) (x : IncSeq) :
    ∃ k q q',
      PowerCopiedLeft r h x 0 k = .atom q ∧
      PowerCopiedLeft r h x 1 k = .atom q' ∧
      q ∈ PowerSupport (h x) := by
-- BODY
  sorry
