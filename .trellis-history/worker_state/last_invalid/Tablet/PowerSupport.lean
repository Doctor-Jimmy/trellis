import Tablet.PowerQ

universe u

-- [TABLET NODE: PowerSupport]
def PowerSupport {Q : Type u} : PowerQ Q → Set Q :=
-- BODY
  fun x => match x with
    | .atom q => {q}
    | .node _ _ f => ⋃ i, PowerSupport (f i)
