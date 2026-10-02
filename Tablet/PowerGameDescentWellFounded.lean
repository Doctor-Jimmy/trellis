import Tablet.PowerGameDescent
import Tablet.PowerChildWellFounded

universe u

-- [TABLET NODE: PowerGameDescentWellFounded]
theorem PowerGameDescentWellFounded {Q : Type u} :
    WellFounded (@PowerGameDescent Q) := by
-- BODY
  apply WellFounded.intro
  intro p
  rcases p with ⟨a, b⟩
  refine (PowerChildWellFounded.induction
    (C := fun a => ∀ b, Acc (@PowerGameDescent Q) (a, b)) a ?_) b
  intro a ih
  intro b
  refine PowerChildWellFounded.induction
    (C := fun b => Acc (@PowerGameDescent Q) (a, b)) b ?_
  intro b ihb
  apply Acc.intro
  intro p hp
  rcases p with ⟨a', b'⟩
  change PowerChild a' a ∨ (a' = a ∧ PowerChild b' b) at hp
  rcases hp with hfirst | ⟨ha, hsecond⟩
  · exact ih a' hfirst b'
  · subst a'
    exact ihb b' hsecond
