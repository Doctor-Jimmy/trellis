import Tablet.PowerCopiedFailureMove
import Tablet.PowerCopiedTerminalAt
import Tablet.PowerGameDescentWellFounded

universe u

-- [TABLET NODE: PowerCopiedTerminates]
theorem PowerCopiedTerminates {Q : Type u} (r : Q → Q → Prop)
    (h : MultiSequence (PowerQ Q))
    (hbad : BadMultiSequence (PowerRel r) h) (x : IncSeq) (n : Nat) :
    ∃ k, PowerCopiedTerminalAt r h x n k := by
-- BODY
  sorry
