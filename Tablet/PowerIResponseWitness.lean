import Tablet.PowerIResponse
import Tablet.PowerRelAtomAtom
import Tablet.PowerRelAtomNode
import Tablet.PowerRelNodeAtom
import Tablet.PowerRelNodeNode

universe u

-- [TABLET NODE: PowerIResponseWitness]
theorem PowerIResponseWitness {Q : Type u} (r : Q → Q → Prop)
    {x y : PowerQ Q} :
    ¬ PowerRel r x y →
      ∃ x', PowerMove x x' ∧
        ∀ y', PowerMove y y' → ¬ PowerRel r x' y' := by
-- BODY
  sorry
