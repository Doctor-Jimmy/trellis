import Tablet.HerCtblPower
import Tablet.PowerRel

universe u

-- [TABLET NODE: HerCtblRel]
def HerCtblRel {Q : Type u} (r : Q → Q → Prop)
    (x y : HerCtblPower Q) : Prop :=
-- BODY
  PowerRel r x.1 y.1
