import Tablet.PowerRelCongrRight

universe u

-- [TABLET NODE: PowerRelRefl]
theorem PowerRelRefl {Q : Type u} (r : Q → Q → Prop) [IsPreorder Q r]
    (x : PowerQ Q) : PowerRel r x x := by
-- BODY
  sorry
