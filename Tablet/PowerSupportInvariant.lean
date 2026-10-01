import Tablet.PowerPresentationEq
import Tablet.PowerSupport

universe u

-- [TABLET NODE: PowerSupportInvariant]
theorem PowerSupportInvariant {Q : Type u} {x y : PowerQ Q} :
    PowerPresentationEq x y → PowerSupport x = PowerSupport y := by
-- BODY
  sorry
