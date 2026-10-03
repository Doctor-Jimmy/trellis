import Tablet.PowerRel

universe u

-- [TABLET NODE: PowerRelNodeAtom]
theorem PowerRelNodeAtom {Q : Type u} (r : Q → Q → Prop)
    {ι : Type u} (h : Nonempty ι) (f : ι → PowerQ Q) (q : Q) :
    PowerRel r (.node ι h f) (.atom q) ↔
      ∀ i, PowerRel r (f i) (.atom q) := by
-- BODY
  unfold PowerRel
  rw [WellFounded.fix_eq]
