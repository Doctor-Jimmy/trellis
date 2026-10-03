import Tablet.PowerChild
import Tablet.PowerRel

universe u

-- [TABLET NODE: PowerMove]
def PowerMove {Q : Type u} : PowerQ Q → PowerQ Q → Prop :=
-- BODY
  fun x x' => match x with
    | .atom q => x' = .atom q
    | .node ι h f => PowerChild x' (.node ι h f)
