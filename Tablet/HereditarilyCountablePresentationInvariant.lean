import Tablet.HereditarilyCountable
import Tablet.PowerPresentationEqEquivalence

universe u

-- [TABLET NODE: HereditarilyCountablePresentationInvariant]
theorem HereditarilyCountablePresentationInvariant {Q : Type u}
    {x y : PowerQ Q} (hxy : PowerPresentationEq x y) :
    HereditarilyCountable x ↔ HereditarilyCountable y := by
-- BODY
  constructor
  · rintro ⟨c, hxc⟩
    exact ⟨c, PowerPresentationEqEquivalence.trans
      (PowerPresentationEqEquivalence.symm hxy) hxc⟩
  · rintro ⟨c, hyc⟩
    exact ⟨c, PowerPresentationEqEquivalence.trans hxy hyc⟩
