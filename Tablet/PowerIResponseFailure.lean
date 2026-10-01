import Tablet.PowerIResponseLegal

universe u

-- [TABLET NODE: PowerIResponseFailure]
theorem PowerIResponseFailure {Q : Type u} (r : Q → Q → Prop)
    {x y : PowerQ Q} (hxy : ¬ PowerRel r x y) {y' : PowerQ Q}
    (hy : PowerMove y y') :
    ¬ PowerRel r (PowerIResponse r x y) y' := by
-- BODY
  sorry
