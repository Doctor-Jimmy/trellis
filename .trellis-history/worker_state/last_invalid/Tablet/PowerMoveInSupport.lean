import Tablet.PowerMove
import Tablet.PowerChildSupport

universe u

-- [TABLET NODE: PowerMoveInSupport]
theorem PowerMoveInSupport {Q : Type u} {x x' : PowerQ Q} :
    PowerMove x x' → PowerSupport x' ⊆ PowerSupport x := by
-- BODY
  intro hmove
  cases x with
  | atom q =>
      have hx' : x' = .atom q := by
        simpa [PowerMove] using hmove
      subst x'
      exact Set.Subset.rfl
  | node ι hι f =>
      exact PowerChildSupport hmove
