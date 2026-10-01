import Tablet.PowerSupport

universe u

-- [TABLET NODE: PowerSupportEquations]
theorem PowerSupportEquations {Q : Type u} :
    (∀ q : Q, PowerSupport (.atom q) = ({q} : Set Q)) ∧
      (∀ (ι : Type u) (hι : Nonempty ι) (f : ι → PowerQ Q),
        PowerSupport (.node ι hι f) = ⋃ i, PowerSupport (f i)) := by
-- BODY
  sorry
