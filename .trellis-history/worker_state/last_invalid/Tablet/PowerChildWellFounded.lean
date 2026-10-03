import Tablet.PowerChild

universe u

-- [TABLET NODE: PowerChildWellFounded]
theorem PowerChildWellFounded {Q : Type u} :
    WellFounded (@PowerChild Q) := by
-- BODY
  apply WellFounded.intro
  intro y
  induction y with
  | atom q =>
      apply Acc.intro
      intro x hx
      simp [PowerChild] at hx
  | node ι h f ih =>
      apply Acc.intro
      intro x hx
      rcases hx with ⟨i, rfl⟩
      exact ih i
