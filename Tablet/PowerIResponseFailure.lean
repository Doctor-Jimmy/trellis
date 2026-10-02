import Tablet.PowerIResponseLegal

universe u

-- [TABLET NODE: PowerIResponseFailure]
theorem PowerIResponseFailure {Q : Type u} (r : Q → Q → Prop)
    {x y : PowerQ Q} (hxy : ¬ PowerRel r x y) {y' : PowerQ Q}
    (hy : PowerMove y y') :
    ¬ PowerRel r (PowerIResponse r x y) y' := by
-- BODY
  classical
  rcases PowerIResponseWitness r hxy with ⟨x', hx', hfail⟩
  have hex : ∃ x', PowerMove x x' ∧
      ∀ y', PowerMove y y' → ¬ PowerRel r x' y' :=
    ⟨x', hx', hfail⟩
  unfold PowerIResponse
  split
  · rename_i h
    exact (Classical.choose_spec h).2 y' hy
  · rename_i h
    exact False.elim (h hex)
