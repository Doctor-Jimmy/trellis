import Tablet.PowerCopiedLeft

universe u

-- [TABLET NODE: PowerCopiedTerminalAt]
def PowerCopiedTerminalAt {Q : Type u} (r : Q → Q → Prop)
    (h : MultiSequence (PowerQ Q)) (x : IncSeq) (n k : Nat) : Prop :=
-- BODY
  ∃ q q', PowerCopiedLeft r h x n k = .atom q ∧
    PowerCopiedLeft r h x (n + 1) k = .atom q'
