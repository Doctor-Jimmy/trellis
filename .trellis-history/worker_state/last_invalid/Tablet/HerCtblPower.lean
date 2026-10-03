import Tablet.HereditarilyCountable

universe u

-- [TABLET NODE: HerCtblPower]
def HerCtblPower (Q : Type u) :=
-- BODY
  {x : PowerQ Q // HereditarilyCountable x}
