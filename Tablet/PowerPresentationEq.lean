import Tablet.PowerQ

universe u

-- [TABLET NODE: PowerPresentationEq]
def PowerPresentationEq {Q : Type u} : PowerQ Q → PowerQ Q → Prop :=
-- BODY
  fun x y => match x, y with
    | .atom q, .atom q' => q = q'
    | .atom _, .node _ _ _ => False
    | .node _ _ _, .atom _ => False
    | .node _ _ f, .node _ _ g =>
        (∀ i, ∃ j, PowerPresentationEq (f i) (g j)) ∧
          (∀ j, ∃ i, PowerPresentationEq (f i) (g j))
