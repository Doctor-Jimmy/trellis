import Tablet.PowerPresentationEq

universe u

-- [TABLET NODE: PowerPresentationEqShape]
theorem PowerPresentationEqShape {Q : Type u} :
    (∀ (q : Q) (ι : Type u) (hι : Nonempty ι) (f : ι → PowerQ Q),
      ¬ PowerPresentationEq (.atom q) (.node ι hι f)) ∧
      (∀ (q : Q) (ι : Type u) (hι : Nonempty ι) (f : ι → PowerQ Q),
        ¬ PowerPresentationEq (.node ι hι f) (.atom q)) ∧
      (∀ (ι κ : Type u) (hι : Nonempty ι) (hκ : Nonempty κ)
        (f : ι → PowerQ Q) (g : κ → PowerQ Q),
        PowerPresentationEq (.node ι hι f) (.node κ hκ g) ↔
          ((∀ i, ∃ j, PowerPresentationEq (f i) (g j)) ∧
            (∀ j, ∃ i, PowerPresentationEq (f i) (g j)))) := by
-- BODY
  sorry
