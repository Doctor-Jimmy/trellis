import Tablet.PowerRel

universe u

-- [TABLET NODE: PowerRelNodeNode]
theorem PowerRelNodeNode {Q : Type u} (r : Q → Q → Prop)
    {ι κ : Type u} (h : Nonempty ι) (h' : Nonempty κ)
    (f : ι → PowerQ Q) (g : κ → PowerQ Q) :
    PowerRel r (.node ι h f) (.node κ h' g) ↔
      ∀ i, ∃ j, PowerRel r (f i) (g j) := by
-- BODY
  unfold PowerRel
  rw [WellFounded.fix_eq]
