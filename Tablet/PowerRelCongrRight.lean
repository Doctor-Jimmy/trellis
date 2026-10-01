import Tablet.PowerRelCongrLeft

universe u

-- [TABLET NODE: PowerRelCongrRight]
theorem PowerRelCongrRight {Q : Type u} (r : Q → Q → Prop)
    {x y y' : PowerQ Q} (hyy' : PowerPresentationEq y y') :
    PowerRel r x y ↔ PowerRel r x y' := by
-- BODY
  sorry
