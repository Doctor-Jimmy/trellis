import Tablet.PowerIResponseWitness

universe u

-- [TABLET NODE: PowerIResponseLegal]
theorem PowerIResponseLegal {Q : Type u} (r : Q → Q → Prop)
    {x y : PowerQ Q} (hxy : ¬ PowerRel r x y) :
    PowerMove x (PowerIResponse r x y) := by
-- BODY
  sorry
