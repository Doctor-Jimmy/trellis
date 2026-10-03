import Tablet.PowerIResponseWitness

universe u

-- [TABLET NODE: PowerIResponseLegal]
theorem PowerIResponseLegal {Q : Type u} (r : Q → Q → Prop)
    {x y : PowerQ Q} (hxy : ¬ PowerRel r x y) :
    PowerMove x (PowerIResponse r x y) := by
-- BODY
  classical
  rcases PowerIResponseWitness r hxy with ⟨x', hx', hfail⟩
  have hex : ∃ x', PowerMove x x' ∧
      ∀ y', PowerMove y y' → ¬ PowerRel r x' y' :=
    ⟨x', hx', hfail⟩
  unfold PowerIResponse
  split
  · rename_i h
    exact (Classical.choose_spec h).1
  · rename_i h
    exact False.elim (h hex)
