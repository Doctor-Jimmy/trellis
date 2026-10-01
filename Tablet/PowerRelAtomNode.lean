import Tablet.PowerRel

universe u

-- [TABLET NODE: PowerRelAtomNode]
theorem PowerRelAtomNode {Q : Type u} (r : Q → Q → Prop) (q : Q)
    {ι : Type u} (h : Nonempty ι) (g : ι → PowerQ Q) :
    PowerRel r (.atom q) (.node ι h g) ↔
      ∃ i, PowerRel r (.atom q) (g i) := by
-- BODY
  unfold PowerRel
  rw [WellFounded.fix_eq]
