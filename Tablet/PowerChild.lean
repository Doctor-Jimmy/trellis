import Tablet.PowerQ

universe u

-- [TABLET NODE: PowerChild]
def PowerChild {Q : Type u} : PowerQ Q → PowerQ Q → Prop :=
-- BODY
  fun x y => match y with
    | .atom _ => False
    | .node _ _ f => ∃ i, x = f i
