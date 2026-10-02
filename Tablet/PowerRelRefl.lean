import Tablet.PowerRelCongrRight

universe u

-- [TABLET NODE: PowerRelRefl]
theorem PowerRelRefl {Q : Type u} (r : Q → Q → Prop) [IsPreorder Q r]
    (x : PowerQ Q) : PowerRel r x x := by
-- BODY
  induction x using PowerChildWellFounded.induction with
  | h x ih =>
    cases x with
    | atom q =>
        rw [PowerRelAtomAtom]
        exact refl q
    | node ι h f =>
        rw [PowerRelNodeNode]
        intro i
        exact ⟨i, ih (f i) ⟨i, rfl⟩⟩
