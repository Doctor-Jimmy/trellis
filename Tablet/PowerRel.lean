import Tablet.PowerChildWellFounded

universe u

-- [TABLET NODE: PowerRel]
def PowerRel {Q : Type u} (r : Q → Q → Prop) (x y : PowerQ Q) : Prop :=
-- BODY
  WellFounded.fix (C := fun _ : PowerQ Q × PowerQ Q => Prop)
    (WellFounded.prod_lex PowerChildWellFounded PowerChildWellFounded)
    (fun p rec => by
      rcases p with ⟨x, y⟩
      cases x with
      | atom q =>
        cases y with
        | atom q' => exact r q q'
        | node ι h g =>
          exact ∃ i, rec (.atom q, g i)
            (Prod.Lex.right _
              (show @PowerChild Q (g i) (.node ι h g) from ⟨i, rfl⟩))
      | node ι h f =>
        cases y with
        | atom q =>
          exact ∀ i, rec (f i, .atom q)
            (Prod.Lex.left _ _
              (show @PowerChild Q (f i) (.node ι h f) from ⟨i, rfl⟩))
        | node κ h' g =>
          exact ∀ i, ∃ j, rec (f i, g j)
            (Prod.Lex.left _ _
              (show @PowerChild Q (f i) (.node ι h f) from ⟨i, rfl⟩)))
    (x, y)
