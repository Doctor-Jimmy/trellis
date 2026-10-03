import Tablet.PowerRel

universe u

-- [TABLET NODE: PowerRelAtomAtom]
theorem PowerRelAtomAtom {Q : Type u} (r : Q → Q → Prop) (q q' : Q) :
    PowerRel r (.atom q) (.atom q') ↔ r q q' := by
-- BODY
  unfold PowerRel
  rw [WellFounded.fix_eq]
