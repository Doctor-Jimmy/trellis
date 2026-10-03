import Tablet.PowerSupport
import Tablet.PowerChild

universe u

-- [TABLET NODE: PowerChildSupport]
theorem PowerChildSupport {Q : Type u} {x y : PowerQ Q} :
    PowerChild x y → PowerSupport x ⊆ PowerSupport y := by
-- BODY
  intro hxy
  cases y with
  | atom q =>
      simp [PowerChild] at hxy
  | node ι hι f =>
      rcases hxy with ⟨i, rfl⟩
      intro q hq
      exact Set.mem_iUnion.2 ⟨i, hq⟩
