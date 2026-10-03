import Tablet.PowerCopiedFiniteTerminal
import Tablet.PowerCopiedShiftIdentity

universe u

-- [TABLET NODE: PowerCopiedTerminalShift]
theorem PowerCopiedTerminalShift {Q : Type u} (r : Q → Q → Prop)
    (h : MultiSequence (PowerQ Q))
    (hbad : BadMultiSequence (PowerRel r) h) (x : IncSeq) :
    ∃ k q q',
      PowerCopiedLeft r h x 0 k = .atom q ∧
      PowerCopiedLeft r h x 1 k = .atom q' ∧
      PowerCopiedLeft r h (ShiftMap x) 0 k = .atom q' := by
-- BODY
  obtain ⟨k, q, q', hq, hq', _⟩ :=
    PowerCopiedFiniteTerminal r h hbad x
  refine ⟨k, q, q', hq, hq', ?_⟩
  calc
    PowerCopiedLeft r h (ShiftMap x) 0 k =
        PowerCopiedLeft r h x (0 + 1) k :=
      PowerCopiedShiftIdentity r h x 0 k
    _ = PowerCopiedLeft r h x 1 k := by simp
    _ = .atom q' := hq'
