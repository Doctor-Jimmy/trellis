import Tablet.PowerRelAtomAtom
import Tablet.PowerRelAtomNode
import Tablet.PowerRelNodeAtom
import Tablet.PowerRelNodeNode
import Tablet.PowerPresentationEqEquivalence

universe u

-- [TABLET NODE: PowerRelCongrLeft]
theorem PowerRelCongrLeft {Q : Type u} (r : Q → Q → Prop)
    {x x' y : PowerQ Q} (hxx' : PowerPresentationEq x x') :
    PowerRel r x y ↔ PowerRel r x' y := by
-- BODY
  sorry
