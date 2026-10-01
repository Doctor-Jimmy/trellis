import Tablet.HerCtblRel
import Tablet.PowerQIsPreorder

universe u

-- [TABLET NODE: HerCtblPowerIsPreorder]
instance HerCtblPowerIsPreorder {Q : Type u} (r : Q → Q → Prop)
    [IsPreorder Q r] : IsPreorder (HerCtblPower Q) (HerCtblRel r) where
-- BODY
  refl := by
    intro x
    exact PowerRelRefl r x.1
  trans := by
    intro x y z hxy hyz
    exact PowerRelTrans r x.1 y.1 z.1 hxy hyz
