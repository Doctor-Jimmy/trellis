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
  rcases PowerCopiedTerminates r h hbad x 0 with ⟨k, hk⟩
  rcases hk with ⟨q, q', hq, hq'⟩
  refine ⟨k, q, q', hq, hq', ?_⟩
  have hsub := PowerCopiedSupport r h hbad x 0 k
  have hsub' : PowerSupport (.atom q) ⊆ PowerSupport (h x) := by
    simpa [PowerShiftIter, hq] using hsub
  exact hsub' (by simp [PowerSupport])
