import Tablet.PowerChild

universe u

-- [TABLET NODE: PowerGameDescent]
def PowerGameDescent {Q : Type u}
    (p q : PowerQ Q × PowerQ Q) : Prop :=
-- BODY
  PowerChild p.1 q.1 ∨ (p.1 = q.1 ∧ PowerChild p.2 q.2)
