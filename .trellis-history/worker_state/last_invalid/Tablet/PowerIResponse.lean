import Tablet.PowerMove

universe u

-- [TABLET NODE: PowerIResponse]
noncomputable def PowerIResponse {Q : Type u} (r : Q → Q → Prop)
    (x y : PowerQ Q) : PowerQ Q :=
-- BODY
  by
    classical
    exact if h : ∃ x', PowerMove x x' ∧
        ∀ y', PowerMove y y' → ¬ PowerRel r x' y' then
      Classical.choose h
    else x
