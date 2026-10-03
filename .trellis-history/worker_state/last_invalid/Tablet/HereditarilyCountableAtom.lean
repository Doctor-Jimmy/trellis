import Tablet.HereditarilyCountable
import Tablet.PowerPresentationEqEquivalence

universe u

-- [TABLET NODE: HereditarilyCountableAtom]
theorem HereditarilyCountableAtom {Q : Type u} (q : Q) :
    HereditarilyCountable (.atom q) := by
-- BODY
  exact ⟨.atom q, PowerPresentationEqEquivalence.refl (.atom q)⟩
