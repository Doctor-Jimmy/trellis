import Tablet.PowerRelRefl

universe u

-- [TABLET NODE: PowerRelTrans]
theorem PowerRelTrans {Q : Type u} (r : Q → Q → Prop) [IsPreorder Q r]
    (x y z : PowerQ Q) :
    PowerRel r x y → PowerRel r y z → PowerRel r x z := by
-- BODY
  sorry
